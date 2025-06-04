// I DO NOT THINK THIS FILE IS A GOOD IDEA. THE TWO REPRESENTATIONS ARE TOO DIFFERENT

package rise.eqsat

import ElevateEqsat._ 

class RewriteS(val name: String,
              val searcher: SearcherS,
              val applier: ApplierS){
  override def toString: String = s"$name:\n$searcher\n  -->\n$applier"

  def requiredAnalyses(): (Set[Analysis], Set[TypeAnalysis]) =
    applier.requiredAnalyses()

  def search(egraph: EGraph,
             worklist: List[SPair]): List[SMatches] = 
    searcher.search(egraph, worklist)

  def apply(sgraph: SGraph,
            matches: List[SMatches]): List[SPair] = // return and matches type to slightly modify
    applier.applyMatches(sgraph, matches)
}

/** The left-hand side of a [[RewriteS]] rule.
  * A searcher is something that can search the [[EGraph]] for
  * matching substitutions.
  */
trait SearcherS {
  // the variables bound by this searcher
  def patternVars(): Set[Any]

  
  // search one sterm, returning an empty list if no matches can be found, corresponds to smatching_aux
  def searchSTerm(egraph: EGraph,
                   shc: Substitutions,
                   sterm: STerm)
                   (S: List[shc.Substitution]): List[shc.Substitution]

  
  // search the whole worklist, returning all matches
  def search(egraph: EGraph, worklist: List[SPair]): List[SMatches]  = // corresponds to classical_smatching
    {
        def treat_worklist(eg: EGraph, wl: List[SPair], aux: List[SMatches]) : List[SMatches] = {
            val shc = SubstitutionsVM
            worklist match {
                case Nil => aux;
                case head :: next => {
                    val substs = (searchSTerm(eg, shc, head.sterm)(SubstitutionVM.empty :: Nil))
                    if (substs != Nil) {
                        treat_worklist(eg, next, SMatches(head,substs)::aux)
                    } else { // if we don't match any substitution, why bother?
                        treat_worklist(eg, next, aux)
                    }
                };
            }
        }

        treat_worklist(egraph, worklist, Nil)
    }
}

/** The right-hand side of a [[RewriteS]] rule.
  * An applier is anything that can use a [[Substitution]] to modify the [[SGraph]].
  */
trait ApplierS {
  // the variables used by this applier
  // return empty to disable checks
  def patternVars(): Set[Any]

  def requiredAnalyses(): (Set[Analysis], Set[TypeAnalysis])

  // Apply a single substitition.
  //
  // An `Applier` should only add things to the egraph here,
  // _not_ union them with the id `eclass`.
  //
  // This should return a list of eclasses you'd like to
  // be unioned with `eclass`. There can be zero, one, or many.
  //
  // `subst` may be modified
  
  def applyOne(sgraph: SGraph,
               sterm : STerm,
               subst: SubstitutionsVM.Substitution,
               worklist: List[STerm]): List[STerm] // corresponds to s_apply_one

  // the substitutions inside `matches` may be modified
  // corresponds to s_apply_all
  def applyMatches(sgraph: SGraph,
                   matches: List[SMatches]): List[SPair] = matches match {
        case Nil => Nil;
        case head :: next => {
            val origin = head.spair.origin 
            val sterm = head.spair.sterm
            val substs = head.substs
            var applied_all_substs : List[STerm] = Nil 
            for (sigma <- substs) {
                applied_all_substs = applyOne(sgraph, sterm, sigma, applied_all_substs)
            };
            val new_spairs = applied_all_substs.map(term => SPair(origin, term))
            new_spairs ::: (applyMatches(sgraph, next))
        };
    }
}

/** An [[ApplierS]] that checks a condition before applying another [[Applier]] */
abstract class ConditionalApplierS(condPatternVars: Set[Any],
                                  condRequiredAnalyses: (Set[Analysis], Set[TypeAnalysis]),
                                  applier: ApplierS)
  extends ApplierS {
  override def toString: String = s"$applier when .."

  def cond(sgraph: SGraph, sterm : STerm)(subst: SubstitutionsVM.Substitution): Boolean

  override def patternVars(): Set[Any] =
    applier.patternVars() ++ condPatternVars

  override def requiredAnalyses(): (Set[Analysis], Set[TypeAnalysis]) = {
    Analysis.mergeRequired(condRequiredAnalyses, applier.requiredAnalyses())
  }

  override def applyOne(sgraph: SGraph,
                        sterm: STerm,
                        subst: SubstitutionsVM.Substitution,
                        worklist: List[STerm]): List[STerm] = {
    if (cond(sgraph, sterm)(subst)) { applier.applyOne(sgraph, sterm, subst, worklist) } else { Nil }
  }
  }

  /** An [[ApplierS]] that shifts the DeBruijn indices of a variable */
case class ShiftedApplierS(v: PatternVar, newV: PatternVar,
                          shift: Expr.Shift, cutoff: Expr.Shift,
                          applier: ApplierS)
  extends ApplierS {
  override def patternVars(): Set[Any] =
    applier.patternVars() - newV + v

  override def requiredAnalyses(): (Set[Analysis], Set[TypeAnalysis]) = ???

  override def applyOne(sgraph: SGraph,
                        sterm: STerm,
                        subst: SubstitutionsVM.Substitution,
                        worklist: List[STerm]): List[STerm] = {
    ??? // subst.insert(newV, EClass.shifted(subst(v), shift, cutoff, egraph)
    applier.applyOne(sgraph, sterm, subst, worklist)
  }
}
/*
/** An [[ApplierS]] that shifts the DeBruijn indices of a variable.
  * @note It works by extracting an expression from the [[EGraph]] in order to shift it.
  */
case class ShiftedExtractApplierS(v: PatternVar, newV: PatternVar,
                                 shift: Expr.Shift, cutoff: Expr.Shift,
                                 applier: ApplierS)
  extends ApplierS {
  override def patternVars(): Set[Any] =
    applier.patternVars() - newV + v

  override def requiredAnalyses(): (Set[Analysis], Set[TypeAnalysis]) =
    Analysis.mergeRequired(applier.requiredAnalyses(), (Set(SmallestSizeAnalysis), Set()))

  override def applyOne(egraph: EGraph,
                        eclass: EClassId,
                        shc: Substs)(
                        subst: shc.Subst): Vec[EClassId] = {
    val smallestOf = egraph.getAnalysis(SmallestSizeAnalysis)
    val extract = smallestOf(shc.get(v, subst))._1
    val shifted = extract.shifted(egraph, shift, cutoff)
    val subst2 = shc.insert(newV, egraph.addExpr(shifted), subst)
    applier.applyOne(egraph, eclass, shc)(subst2)
  }
}
*/