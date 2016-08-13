// Copyright: 2010 - 2016 https://github.com/ensime/ensime-server/graphs
// License: http://www.gnu.org/licenses/gpl-3.0.en.html
package org.ensime.core

import java.io.File
import org.slf4j.LoggerFactory

import scala.collection.mutable.ListBuffer
import scala.reflect.internal.util.RangePosition
import scala.reflect.io.AbstractFile
import scala.tools.nsc.symtab.Flags._
import scala.tools.refactoring.common.{ CompilerAccess, EnrichedTrees }

import org.ensime.api._

class SemanticHighlighting(val global: RichPresentationCompiler) extends CompilerAccess with EnrichedTrees {
  val log = LoggerFactory.getLogger(getClass)

  import global._

  object MyTraverser extends Traverser {
    override def traverse(t: Tree): Unit = {
      log.debug(s"mytraverse:  ${t.summaryString}")
      log.debug(s"mytraverse:  kids=${t.children}")
      log.debug(s"mytraverse:  symbol=${t.symbol}, ${if (t.symbol != null) t.symbol.isSynthetic}")
      log.debug(s"------------------------------")
      super.traverse(t)
    }
  }

  class SymDesigsTraverser(p: RangePosition, tpeSet: Set[SourceSymbol]) extends Traverser {

    val log = LoggerFactory.getLogger(getClass)
    val syms = ListBuffer[SymbolDesignation]()

    def symbolPriority(sym: SymbolDesignation): Int =
      sym.symType match {
        case ParamSymbol => 90
        case FunctionCallSymbol => 50
        case DeprecatedSymbol => 200
        case _ => 100
      }

    def removeOverlaps(l: ListBuffer[SymbolDesignation]): ListBuffer[SymbolDesignation] = {
      case class Accum(previous: SymbolDesignation, a: ListBuffer[SymbolDesignation])
      def overlapAllowed(sym: SymbolDesignation): Boolean = sym.symType == ImplicitConversionSymbol || sym.symType == ImplicitParamsSymbol
      def helper(accum: Accum, sym: SymbolDesignation): Accum = {
        if (accum.previous.end > sym.start) // Overlap
          if (accum.previous == sym) accum // Remove duplicate
          else if (overlapAllowed(accum.previous) || overlapAllowed(sym))
            Accum(sym, accum.a += accum.previous)
          else if (symbolPriority(accum.previous) < symbolPriority(sym)) {
            log.debug(s"{${p.source}} Removing overlapping ${accum.previous} which conflicts with $sym")
            Accum(sym, accum.a)
          } else if (symbolPriority(accum.previous) > symbolPriority(sym)) {
            log.debug(s"{${p.source}} Removing overlapping ${sym} which conflicts with ${accum.previous}")
            Accum(accum.previous, accum.a)
          } else {
            log.debug(s"{${p.source}} Allowing overlapping  $sym with conflicts with ${accum.previous}")
            Accum(sym, accum.a += accum.previous)
          }
        else Accum(sym, accum.a += accum.previous)
      }

      if (l.size <= 1) l
      else {
        val sorted = l.sortBy(_.start)
        val Accum(sym, accum) = sorted.tail.foldLeft(Accum(sorted.head, ListBuffer[SymbolDesignation]()))(helper)
        accum += sym
      }
    }

    override def traverse(t: Tree): Unit = {
      log.debug(s"traverse: ${t.summaryString} ${t}")
      log.debug(s"traverse: kids=${t.children.map { _.summaryString }}")
      val treeP = t.pos

      def matchesSource(s: String): Boolean = {
        val end = Math.min(t.namePosition.end, t.namePosition.start + s.length)
        p.source.content.subSequence(t.namePosition.start, end).toString == s
      }

      def addAt(start: Int, end: Int, designation: SourceSymbol): Boolean = {
        log.debug(s"addAt:  start=$start, end=$end, designation=$designation, included=${tpeSet.contains(designation)}")
        if (tpeSet.contains(designation)) {
          syms += SymbolDesignation(start, end, designation)
        }
        true
      }

      def add(designation: SourceSymbol): Boolean = {
        log.debug(s"add:  designation=$designation, pos=${t.namePosition()}")
        val pos = t.namePosition()
        addAt(pos.startOrCursor, pos.endOrCursor, designation)
      }

      def qualifySymbol(sym: Symbol): Boolean = {
        log.debug(s"qualifysymbol:  sym=$sym, flags=${sym.flagString}, pos=${treeP}, ${sym.parentSymbols}, ${sym.isSynthetic}, ${sym.isPackageObject}")
        log.debug(s"qualifySymbol:  ${sym.nameString} == ${matchesSource(sym.nameString)}")
        if (sym == NoSymbol) {
          false
        } else if (sym.isCaseApplyOrUnapply) {
          logger.debug(s"qualifySymbol:  owner=${sym.owner}")
          val owner = sym.owner
          val start = treeP.startOrCursor
          val end = start + owner.name.length
          addAt(start, end, ObjectSymbol)
        } else if (sym.isConstructor && !treeP.isTransparent) {
          addAt(treeP.startOrCursor, treeP.endOrCursor, ConstructorSymbol)
        } else if (sym.isTypeParameterOrSkolem && matchesSource(sym.nameString)) {
          add(TypeParamSymbol)
        } else if (sym.hasFlag(PARAM) && matchesSource(sym.nameString)) {
          add(ParamSymbol)
        } else {

          if (sym.ownerChain.exists(_.isDeprecated)) {
            add(DeprecatedSymbol)
          }

          if (sym.ownerChain.exists(_.annotations.exists(_.atp.toString().endsWith("deprecating")))) {
            add(DeprecatedSymbol)
          }

          if (sym.hasFlag(ACCESSOR) /* && matchesSource(sym.nameString)*/ ) {
            val under = sym.accessed
            // The compiler mis-reports lazy val fields
            // as variables. Lazy can only be a val anyway.
            if (sym.hasFlag(LAZY)) {
              add(ValFieldSymbol)
            } else if (under.isVariable) {
              add(VarFieldSymbol)
            } else if (under.isValue) {
              add(ValFieldSymbol)
            } else {
              false
            }
          } else if (sym.hasFlag(PARAMACCESSOR)) {
            add(ValFieldSymbol)
          } else if (sym.isMethod) {
            if (sym.name.isOperatorName)
              add(OperatorFieldSymbol)
            else if (matchesSource(sym.nameString))
              add(FunctionCallSymbol)
            else
              true
          } else if (sym.isSynthetic) {
            true
          } /* else if (!matchesSource(sym.nameString)) {
            log.debug(s"qualifySymbol:  $sym does not match source ${p.source.content.subSequence(t.namePosition.start, t.namePosition.end).toString}.")
            true
          }*/ else if (sym.isVariable && sym.isLocalToBlock) {
            add(VarSymbol)
          } else if (sym.isValue && sym.isLocalToBlock) {
            add(ValSymbol)
          } else if (sym.hasPackageFlag) {
            add(PackageSymbol)
          } else if (sym.isTrait) {
            add(TraitSymbol)
          } else if (sym.isClass) {
            add(ClassSymbol)
          } else if (sym.isModule) {
            add(ObjectSymbol)
          } else {
            false
          }
        }
      }

      // logger.debug(s"traverse: isTransparent=${treeP.isTransparent}, p.overlaps=${p.overlaps(treeP)}, p=${p}, treeP=$treeP")
      // if ((t.hasSymbolField && !t.symbol.isSynthetic) || !t.hasSymbolField) {
      if (p.overlaps(treeP)) {
        try {
          val sym = t.symbol
          t match {
            case Import(expr, selectors) =>
              for (impSel <- selectors) {
                val start = impSel.namePos
                val end = start + impSel.name.decode.length()
                addAt(start, end, ImportedNameSymbol)
              }

            case Ident(_) =>
              qualifySymbol(sym)

            case Select(_, _) =>
              qualifySymbol(sym)

            case ValDef(mods, name, tpt, rhs) =>
              if (sym != NoSymbol && !sym.isSynthetic) {
                val isField = sym.owner.isType || sym.owner.isModule

                if (mods.hasFlag(PARAM)) {
                  add(ParamSymbol)
                } else if (mods.hasFlag(MUTABLE) && !isField) {
                  add(VarSymbol)
                } else if (!isField) {
                  if (matchesSource(sym.nameString))
                    add(ValSymbol)
                  else true
                } else if (mods.hasFlag(MUTABLE) && isField) {
                  add(VarFieldSymbol)
                } else if (isField) {
                  add(ValFieldSymbol)
                }
              }

            case TypeDef(mods, name, params, rhs) =>
              logger.debug(s"traverseX:  TypeDef($mods, $name, $params, $rhs), ${sym.isSynthetic}, ${sym == NoSymbol}, ${mods.hasFlag(PARAM)}")
              if (!(sym == NoSymbol || sym.isSynthetic)) {
                if (mods.hasFlag(PARAM)) {
                  add(TypeParamSymbol)
                }
              }

            case t: ApplyImplicitView =>
              add(ImplicitConversionSymbol)

            case t: ApplyToImplicitArgs =>
              add(ImplicitParamsSymbol)

            case TypeTree() =>
              logger.debug(s"traverse:  TypeTree - ${sym.isSynthetic}")
              if (!qualifySymbol(sym)) {
                if (t.tpe != null) {
                  val start = treeP.startOrCursor
                  val end = treeP.endOrCursor
                  addAt(start, end, ObjectSymbol)
                }
              }

            case Function(vparams, body) =>
              logger.debug(s"vparams=$vparams, body=$body")

            case _ =>

          }
        } catch {
          case e: Throwable =>
            log.error("Error in AST traverse:", e)
        }
      }
      log.debug(s"traverse: ---------------")
      super.traverse(t)
      // }
    }
  }

  def symbolDesignationsInRegion(
    p: RangePosition,
    requestedTypes: List[SourceSymbol]
  ): SymbolDesignations = {
    val typed = new Response[Tree]
    // AskLoadedTyped below doesn't wait, since this code should run in the pres. compiler thread.
    askLoadedTyped(p.source, keepLoaded = true, typed)

    typed.get.left.toOption match {
      case Some(tree) =>
        // log.debug(s"symboldesignationsinregion: $tree")
        // MyTraverser.traverse(tree)
        log.debug(s"symbolDesignationsInRegion:  types=$requestedTypes")
        val traverser = new SymDesigsTraverser(p, requestedTypes.toSet)
        traverser.traverse(tree)
        SymbolDesignations(p.source.file.file, traverser.removeOverlaps(traverser.syms).toList)
      case None =>
        SymbolDesignations(new File("."), List.empty)
    }
  }

  def compilationUnitOfFile(f: AbstractFile): Option[CompilationUnit] = unitOfFile.get(f)

}
