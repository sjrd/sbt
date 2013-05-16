/* sbt -- Simple Build Tool
 * Copyright 2008, 2009 Mark Harrah
 */
package xsbt

import xsbti.{AnalysisCallback,Logger,Problem,Reporter,Severity}
import xsbti.compile._
import scala.tools.nsc.{backend, io, reporters, symtab, util, Phase, Global, Settings, SubComponent}
import scala.tools.nsc.interactive.RangePositions
import backend.JavaPlatform
import scala.tools.util.PathResolver
import symtab.SymbolLoaders
import util.{ClassPath,DirectoryClassPath,MergedClassPath,JavaClassPath}
import ClassPath.{ClassPathContext,JavaContext}
import io.AbstractFile
import scala.annotation.tailrec
import scala.collection.mutable
import Log.debug
import java.io.File

final class CompilerInterface
{
	def newCompiler(options: Array[String], output: Output, initialLog: Logger, initialDelegate: Reporter, resident: Boolean): CachedCompiler =
		new CachedCompiler0(options, output, new WeakLog(initialLog, initialDelegate), resident)

	def run(sources: Array[File], changes: DependencyChanges, callback: AnalysisCallback, log: Logger, delegate: Reporter, progress: CompileProgress, cached: CachedCompiler): Unit =
		cached.run(sources, changes, callback, log, delegate, progress)
}
// for compatibility with Scala versions without Global.registerTopLevelSym (2.8.1 and earlier)
sealed trait GlobalCompat { self: Global =>
	def registerTopLevelSym(sym: Symbol): Unit
	sealed trait RunCompat {
		def informUnitStarting(phase: Phase, unit: CompilationUnit) {}
	}
}
sealed abstract class CallbackGlobal(settings: Settings, reporter: reporters.Reporter, output: Output) extends Global(settings, reporter) with GlobalCompat {
	def callback: AnalysisCallback
	def findClass(name: String): Option[(AbstractFile,Boolean)]
	lazy val outputDirs: Iterable[File] = {
		output match {
			case single: SingleOutput => List(single.outputDirectory)
			case multi: MultipleOutput => multi.outputGroups.toStream map (_.outputDirectory)
		}
	}
	// Map source files to public inherited dependencies.  These dependencies are tracked as the symbol for the dealiased base class.
	val inheritedDependencies = new mutable.HashMap[File, mutable.Set[Symbol]]
	def addInheritedDependencies(file: File, deps: Iterable[Symbol]) {
		inheritedDependencies.getOrElseUpdate(file, new mutable.HashSet) ++= deps
	}
}
class InterfaceCompileFailed(val arguments: Array[String], val problems: Array[Problem], override val toString: String) extends xsbti.CompileFailed

private final class WeakLog(private[this] var log: Logger, private[this] var delegate: Reporter)
{
	def apply(message: String) {
		assert(log ne null, "Stale reference to logger")
		log.error(Message(message))
	}
	def logger: Logger = log
	def reporter: Reporter = delegate
	def clear() {
		log = null
		delegate = null
	}
}

private final class CachedCompiler0(args: Array[String], output: Output, initialLog: WeakLog, resident: Boolean) extends CachedCompiler
{
	val settings = new Settings(s => initialLog(s))
	output match {
		case multi: MultipleOutput =>
			for (out <- multi.outputGroups)
				settings.outputDirs.add(out.sourceDirectory.getAbsolutePath, out.outputDirectory.getAbsolutePath)
		case single: SingleOutput =>
			settings.outputDirs.setSingleOutput(single.outputDirectory.getAbsolutePath)
	}

	val command = Command(args.toList, settings)
	private[this] val dreporter = DelegatingReporter(settings, initialLog.reporter)
	try {
		if(!noErrors(dreporter)) {
			dreporter.printSummary()
			handleErrors(dreporter, initialLog.logger)
		}
	} finally
		initialLog.clear()

	def noErrors(dreporter: DelegatingReporter) = !dreporter.hasErrors && command.ok

	def commandArguments(sources: Array[File]): Array[String] =
		(command.settings.recreateArgs ++ sources.map(_.getAbsolutePath)).toArray[String]

	def run(sources: Array[File], changes: DependencyChanges, callback: AnalysisCallback, log: Logger, delegate: Reporter, progress: CompileProgress): Unit = synchronized
	{
		debug(log, "Running cached compiler " + hashCode.toHexString + ", interfacing (CompilerInterface) with Scala compiler " + scala.tools.nsc.Properties.versionString)
		val dreporter = DelegatingReporter(settings, delegate)
		try { run(sources.toList, changes, callback, log, dreporter, progress) }
		finally { dreporter.dropDelegate() }
	}
	private[this] def run(sources: List[File], changes: DependencyChanges, callback: AnalysisCallback, log: Logger, dreporter: DelegatingReporter, compileProgress: CompileProgress)
	{
		if(command.shouldStopWithInfo)
		{
			dreporter.info(null, command.getInfoMessage(compiler), true)
			throw new InterfaceCompileFailed(args, Array(), "Compiler option supplied that disabled actual compilation.")
		}
		if(noErrors(dreporter))
		{
			debug(log, args.mkString("Calling Scala compiler with arguments  (CompilerInterface):\n\t", "\n\t", ""))
			compiler.set(callback, dreporter)
			val run = new compiler.Run with compiler.RunCompat {
				override def informUnitStarting(phase: Phase, unit: compiler.CompilationUnit) {
					compileProgress.startUnit(phase.name, unit.source.path)
				}
				override def progress(current: Int, total: Int) {
					if (!compileProgress.advance(current, total))
						cancel
				}
			}
			val sortedSourceFiles = sources.map(_.getAbsolutePath).sortWith(_ < _)
			run compile sortedSourceFiles
			processUnreportedWarnings(run)
			dreporter.problems foreach { p => callback.problem(p.category, p.position, p.message, p.severity, true) }
		}
		dreporter.printSummary()
		if(!noErrors(dreporter)) handleErrors(dreporter, log)
	}
	def handleErrors(dreporter: DelegatingReporter, log: Logger): Nothing =
	{
		debug(log, "Compilation failed (CompilerInterface)")
		throw new InterfaceCompileFailed(args, dreporter.problems, "Compilation failed")
	}
	def processUnreportedWarnings(run: compiler.Run)
	{
			// allConditionalWarnings and the ConditionalWarning class are only in 2.10+
			final class CondWarnCompat(val what: String, val warnings: mutable.ListBuffer[(compiler.Position, String)])
			implicit def compat(run: AnyRef): Compat = new Compat
			final class Compat { def allConditionalWarnings = List[CondWarnCompat]() }

		val warnings = run.allConditionalWarnings
		if(!warnings.isEmpty)
			compiler.logUnreportedWarnings(warnings.map(cw => ("" /*cw.what*/, cw.warnings.toList)))
	}

	val compiler: Compiler = {
		def getSettingsDefines(name: String): List[String] = {
			implicit def compat28x(definePair: (String, String)): String =
				"-D" + definePair._1 + "=" + definePair._2

			val prefix = "-D"+name+"="
			for {
				define <- command.settings.defines.value
				if define.substring(0, prefix.length) == prefix
			} yield {
				define.substring(prefix.length)
			}
		}

		def getSettingsDefine(name: String, default: String = ""): String = {
			getSettingsDefines(name).headOption.getOrElse(default)
		}

		val dynamicCompilerTrait = getSettingsDefine("sbt.compile.interface.dynamiccompilertrait")
		val dynamicCompilerJar = getSettingsDefine("sbt.compile.interface.dynamiccompilerjar")

		if (dynamicCompilerTrait.isEmpty) {
			if (command.settings.Yrangepos.value)
				new Compiler() with RangePositions // unnecessary in 2.11
			else
				new Compiler()
		} else {
			// Abuse import resolution order and precedence to be compatible with Scala < 2.10
			import CompatReflectBefore210._
			{
			import scala.reflect._ // for runtime.universe
			import scala.tools._   // for reflect.ToolBox
			{
			import runtime.universe._
			import reflect._ // for ToolBox

			val classLoader0 = this.getClass.getClassLoader
			val classLoader =
				if (dynamicCompilerJar.isEmpty) classLoader0
				else new java.net.URLClassLoader(Array(new File(dynamicCompilerJar).toURI.toURL), classLoader0)

			val cm = runtimeMirror(classLoader)
			val tb = cm.mkToolBox()

			val thisTerm = build.newFreeTerm("thisCachedCompiler0", this)
			build.setTypeSignature(thisTerm, typeOf[CachedCompiler0])

			tb.eval {
				val maybeRangePosParent =
					if (command.settings.Yrangepos.value) List(TypeTree(typeOf[RangePositions]))
					else Nil

				val dynamicCompilerTraitType =
					cm.staticClass(dynamicCompilerTrait).toTypeConstructor

				val specializedCompilerParents = (
					Select(Ident(newTermName("localThis")), newTypeName("Compiler")) ::
					TypeTree(dynamicCompilerTraitType) ::
					maybeRangePosParent)

				val emptyConstructor =
					DefDef(Modifiers(), nme.CONSTRUCTOR, List(), List(List()), TypeTree(),
					Block(List(Apply(Select(Super(This(tpnme.EMPTY), tpnme.EMPTY), nme.CONSTRUCTOR), List())), Literal(Constant(()))))

				Block(List(
					// val localThis = thisCachedCompiler0
					ValDef(Modifiers(), newTermName("localThis"), TypeTree(), Ident(thisTerm)),
					// class SpecializedCompiler extends localThis.Compiler with $dynamicCompilerTrait (with RangePositions)
					ClassDef(Modifiers(Flag.FINAL), newTypeName("SpecializedCompiler"), List(), Template(
						specializedCompilerParents,
						emptyValDef,
						List(emptyConstructor)))),
					// new SpecializedCompiler
					Apply(Select(New(Ident(newTypeName("SpecializedCompiler"))), nme.CONSTRUCTOR), List()))
			}.asInstanceOf[Compiler]
			}
			}
		}
	}
	class Compiler extends CallbackGlobal(command.settings, dreporter, output)
	{
		object dummy // temporary fix for #4426
		object sbtAnalyzer extends
		{
			val global: Compiler.this.type = Compiler.this
			val phaseName = Analyzer.name
			val runsAfter = List("jvm")
			override val runsBefore = List("terminal")
			val runsRightAfter = None
		}
		with SubComponent
		{
			val analyzer = new Analyzer(global)
			def newPhase(prev: Phase) = analyzer.newPhase(prev)
			def name = phaseName
		}
		/** This phase walks trees and constructs a representation of the public API, which is used for incremental recompilation.
		 *
		 * We extract the api after picklers, since that way we see the same symbol information/structure
		 * irrespective of whether we were typechecking from source / unpickling previously compiled classes.
		 */
		object apiExtractor extends
		{
			val global: Compiler.this.type = Compiler.this
			val phaseName = API.name
			val runsAfter = List("typer")
			override val runsBefore = List("erasure")
			// allow apiExtractor's phase to be overridden using the sbt.api.phase property
			// (in case someone would like the old timing, which was right after typer)
			// TODO: consider migrating to simply specifying "pickler" for `runsAfter` and "uncurry" for `runsBefore`
			val runsRightAfter = Option(System.getProperty("sbt.api.phase")) orElse Some("pickler")
		}
		with SubComponent
		{
			val api = new API(global)
			def newPhase(prev: Phase) = api.newPhase(prev)
			def name = phaseName
		}

		override lazy val phaseDescriptors =
		{
			phasesSet += sbtAnalyzer
			phasesSet += apiExtractor
			superComputePhaseDescriptors
		}
		// Required because computePhaseDescriptors is private in 2.8 (changed to protected sometime later).
		private[this] def superComputePhaseDescriptors() = superCall("computePhaseDescriptors").asInstanceOf[List[SubComponent]]
		private[this] def superDropRun(): Unit =
			try { superCall("dropRun") } catch { case e: NoSuchMethodException => () } // dropRun not in 2.8.1
		private[this] def superCall(methodName: String): AnyRef =
		{
			val meth = classOf[Global].getDeclaredMethod(methodName)
			meth.setAccessible(true)
			meth.invoke(this)
		}
		def logUnreportedWarnings(seq: Seq[(String, List[(Position,String)])]): Unit = // Scala 2.10.x and later
		{
			val drep = reporter.asInstanceOf[DelegatingReporter]
			for( (what, warnings) <- seq; (pos, msg) <- warnings) yield
				callback.problem(what, drep.convert(pos), msg, Severity.Warn, false)
		}
		
		def set(callback: AnalysisCallback, dreporter: DelegatingReporter)
		{
			this.callback0 = callback
			reporter = dreporter
		}
		def clear()
		{
			callback0 = null
			superDropRun()
			reporter = null
		}

		def findClass(name: String): Option[(AbstractFile, Boolean)] =
			getOutputClass(name).map(f => (f,true)) orElse findOnClassPath(name).map(f =>(f, false))

		def getOutputClass(name: String): Option[AbstractFile] =
		{
			// This could be improved if a hint where to look is given.
			val className = name.replace('.', '/') + ".class"
			outputDirs map (new File(_, className)) find (_.exists) map (AbstractFile.getFile(_))
		}

		def findOnClassPath(name: String): Option[AbstractFile] =
			classPath.findClass(name).flatMap(_.binary.asInstanceOf[Option[AbstractFile]])


		private[this] var callback0: AnalysisCallback = null
		def callback: AnalysisCallback = callback0
	}
}

/** Impersonation of Scala Reflection for compatibility with Scala < 2.10.
 *  This does not make it *work* before 2.10. It only makes sure that this file
 *  can be compiled with earlier versions of Scala.
 */
private[xsbt] object CompatReflectBefore210 {
	private def ??? : Nothing =
		throw new Exception("Dynamic compiler trait mixin is only supported with Scala 2.10+")

	object runtime {
		object universe {
			def runtimeMirror(classLoader: ClassLoader): Mirror = ???
			def typeOf[T]: Any = ???

			object build {
				def newFreeTerm(name: String, value: Any): Any = ???
				def setTypeSignature(sym: Any, tpe: Any): Unit = ???
			}

			class Mirror {
				def mkToolBox(): ToolBox = ???
				def staticClass(name: String): ClassSymbol = ???
			}
			class ClassSymbol {
				def toTypeConstructor: Any = ???
			}
			class ToolBox {
				def eval(tree: Any): Any = ???
			}

			def newTermName(name: String): Any = ???
			def newTypeName(name: String): Any = ???

			def TypeTree(tpe: Any): Any = ???
			def TypeTree(): Any = ???
			def Ident(sym: Any): Any = ???

			def ValDef(mods: Any, name: Any, tpe: Any, rhs: Any): Any = ???
			def DefDef(mods: Any, name: Any, tpt: List[Any], paramss: List[List[Any]], resultType: Any, body: Any): Any = ???
			def ClassDef(mods: Any, name: Any, paramss: List[List[Any]], tpl: Any): Any = ???
			def Template(parents: List[Any], self: Any, members: List[Any]): Any = ???

			def Block(stats: List[Any], expr: Any): Any = ???
			def Select(qual: Any, item: Any): Any = ???
			def Apply(fun: Any, args: List[Any]): Any = ???
			def This(cls: Any): Any = ???
			def Super(obj: Any, mixin: Any): Any = ???
			def Literal(c: Any): Any = ???
			def Constant(value: Any): Any = ???
			def New(tpe: Any): Any = ???

			def Modifiers(): Any = ???
			def Modifiers(flag: Any): Any = ???

			def emptyValDef: Any = ???

			object nme {
				def CONSTRUCTOR: Any = ???
			}
			object tpnme {
				def EMPTY: Any = ???
			}
			object Flag {
				def FINAL: Any = ???
			}
		}
	}

	object reflect {
	}
}
