package rise.eqsat

import elevate.core.strategies.basic.id
//import elevate.core.strategies.traversal._
//import elevate.core.strategies.predicate._ 
//import elevate.core.strategies.debug._
import elevate.core.{Failure, RewriteResult, Strategy, Success}
import rise.elevate.Rise
import rise.elevate.rules.traversal._
//import elevate.core.strategies.Traversable
import elevate.macros.StrategyMacro
// import scala.language.implicitConversions
import GuidedSearch._
import scala.language.existentials
 
object elevate_eqsat {

    /*
    equivalence prover with BENF and CNF 
    */

    def prove_equiv_BENF(rules: Seq[Rewrite], normRules: Seq[RewriteDirected] = BENF.directedRules): Rise => Strategy[Rise] =
        // t is the target, p the input program
        // we make it in this order to be able to compose in a nice way
        t => p => try {
            ProveEquiv.init().runBENF(ProveEquiv.OneOrMore(Seq(p)), ProveEquiv.OneOrMore(Seq(t)), rules, normRules);
            Success(t)
        } catch {
            case _ : Exception => Failure(prove_equiv_BENF(rules,normRules)(t)) //CouldNotProveEquiv
        }
    
    def prove_equiv_CNF(rules: Seq[Rewrite], normRules: Seq[RewriteDirected] = BENF.directedRules): Rise => Strategy[Rise] =
        // t is the target, p the input program
        // we make it in this order to be able to compose in a nice way
        t => p => try {
            ProveEquiv.init().runCNF(ProveEquiv.OneOrMore(Seq(p)), ProveEquiv.OneOrMore(Seq(t)), rules, normRules);
            Success(t)
        } catch {
            case _ : Exception => Failure(prove_equiv_CNF(rules, normRules)(t)) //CouldNotProveEquiv
        }
    
    /* 
    classic equality saturation, with CNF and BENF
    */

    def runCNF: Strategy[Rise] = p => Success(Expr.toNamed(CNF(Expr.fromNamed(p))))

    def runBENF: Strategy[Rise] = p => Success(Expr.toNamed(BENF(Expr.fromNamed(p))._1))

    /* 
    term-guided equality saturation
    */

    def termguided_pe_CNF(rules: Seq[Rewrite], normRules: Seq[RewriteDirected] = CNF.directedRules, l:List[Rise]) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => s `;` prove_equiv_CNF(rules, normRules)(t))

    def termguided_pe_BENF(rules: Seq[Rewrite], normRules: Seq[RewriteDirected] = BENF.directedRules, l:List[Rise]) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => s `;` prove_equiv_BENF(rules, normRules)(t))

    /*
    sketch-guided equality saturation 
    */

    def runOne_acc(filter: Predicate, transformRunner: Runner => Runner, step: GuidedSearch.Step) : Strategy[Rise] = 
    t => {
        val start = Expr.fromNamed(t)
        val startTime = System.nanoTime()
        // note: this is a bit hacky
        val timeLimit = transformRunner(Runner.init()).timeLimit

        var normRewriteCount = 0L
        val (initializeTime, (egraph, rootId)) = util.time{
        val egraph = EGraph.empty()
        val beam = Seq(start)
        val normBeam = beam.map { e =>
            val (n, rc) = step.normalForm.normalizeCountRewrites(e)
            normRewriteCount += rc
            n
            }
        val rootId = normBeam.map(egraph.addExpr)
                    .reduce[EClassId] { case (a, b) => egraph.union(a, b)._1 }
                egraph.rebuild(Seq(rootId))
                (egraph, rootId)
        }

        // TODO: add goal check to e-graph for incremental update?
        val mergedRules = (step.rules ++ step.normalForm.rules).distinctBy(_.name)
        val (growTime, runner) = util.time(transformRunner(Runner.init())
            // note: update time limit
            .withTimeLimit(java.time.Duration.ofNanos(timeLimit - (System.nanoTime() - startTime)))
            .doneWhen { _ =>
            util.printTime("goal check", Sketch.exists(step.sketch, egraph, rootId))
            }.run(egraph, filter, mergedRules, Seq(), Seq(rootId)))
        val found = runner.stopReasons.contains(Done)

        val (extractionTime, newBeam) = if (found) {
                util.time(step.extractor.extract(step.sketch, egraph, rootId))
            } else {
                (0L, Seq())
            }
        if (found) {
            assert(newBeam.nonEmpty)
            Success(Expr.toNamed(newBeam(0))) // one corresponding term
        } else {
            Failure(runOne_acc(filter, transformRunner, step)) // could not reach sketch
        }
    }

    def runOne(filter: Predicate, transformRunner: Runner => Runner, nf : NF, rules: Seq[Rewrite] = Seq(), ex: Extractor = BeamExtractor(1, AstSize), sketch: Sketch = SketchAny(TypePatternAny)) : Strategy[Rise] = 
        runOne_acc(filter, transformRunner, Step.init(nf).withRules(rules).withExtractor(ex).withSketch(sketch))

    def guided_eqsat(filter: Predicate, transformRunner: Runner => Runner, nf : NF, rules: Seq[Rewrite] = Seq(), ex: Extractor = BeamExtractor(1, AstSize), sketches: List[Sketch] = List(SketchAny(TypePatternAny))) : Strategy[Rise] = 
        sketches.foldLeft(id[Rise])((s,t) => s `;` runOne(filter, transformRunner, nf, rules, ex, t))


}