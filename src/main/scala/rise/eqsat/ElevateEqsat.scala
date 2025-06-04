package rise.eqsat

import elevate.core.strategies.basic.{id, `try`, fail}
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
import scala.annotation.tailrec
import fastparse.Parsed
import scala.collection.mutable.HashMap
 //import scala.util.Failure
 
object ElevateEqsat {

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
    classic equality saturation, with just CNF and BENF rules
    */

    def runCNF: Strategy[Rise] = p => Success(Expr.toNamed(CNF(Expr.fromNamed(p))))

    def runBENF: Strategy[Rise] = p => Success(Expr.toNamed(BENF(Expr.fromNamed(p))._1))

    /* 
    term-guided equality saturation
    */

    def termguided_pe_CNF(rules: Seq[Rewrite], l:List[Rise], normRules: Seq[RewriteDirected] = CNF.directedRules) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => s `;` prove_equiv_CNF(rules, normRules)(t))

    def termguided_pe_BENF(rules: Seq[Rewrite], l:List[Rise], normRules: Seq[RewriteDirected] = BENF.directedRules) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => s `;` prove_equiv_BENF(rules, normRules)(t))

    def no_failure_termguided_pe_CNF(rules: Seq[Rewrite], l:List[Rise], normRules: Seq[RewriteDirected] = CNF.directedRules) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => `try`(s `;` prove_equiv_CNF(rules, normRules)(t)))

    def no_failure_termguided_pe_BENF(rules: Seq[Rewrite], l:List[Rise], normRules: Seq[RewriteDirected] = BENF.directedRules) : Strategy[Rise] = 
        // l is the list of guides
        l.foldLeft(id[Rise])((s,t) => `try`(s `;` prove_equiv_BENF(rules, normRules)(t)))

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

    def changing_rules_guided_eqsat(filter: Predicate, transformRunner: Runner => Runner, nf : NF, sketches: List[(Seq[Rewrite],Sketch)], ex: Extractor = BeamExtractor(1, AstSize)) : Strategy[Rise] = //tochange
        sketches.foldLeft(id[Rise])((s,t) => {val (rules, sketch) = t 
                                            s `;` runOne(filter, transformRunner, nf, rules, ex, sketch)})

    def no_failure_guided_eqsat(filter: Predicate, transformRunner: Runner => Runner, nf : NF, rules: Seq[Rewrite] = Seq(), ex: Extractor = BeamExtractor(1, AstSize), sketches: List[Sketch] = List(SketchAny(TypePatternAny))) : Strategy[Rise] =
        sketches.foldLeft(id[Rise])((s,t) => `try`(s `;` runOne(filter, transformRunner, nf, rules, ex, t)))


    // now, let's restrict strategies (as in System S cf Shoggoth paper)

    case class SRewrite(lhs: Pattern, rhs: Pattern)

    sealed trait StrategyS
    case object Skip extends StrategyS
    case object Abort extends StrategyS
    case class RewriteRule(rw: SRewrite) extends StrategyS // Rewrite ~~ (String, (Searcher,Applier)) , shc: Substs
    case class ComposeSeq(s1: StrategyS, s2: StrategyS) extends StrategyS
    case class LeftChoice(s1: StrategyS, s2: StrategyS) extends StrategyS


    object NamedStrategyS {
        def init(name: String, strat: StrategyS): NamedStrategyS = 
            new NamedStrategyS(name, strat)
    }
    
    class NamedStrategyS(val name: String,
                         val strat: StrategyS){
        override def toString(): String = strat match {
            case Skip => " skip ";
            case Abort => " abort ";
            case RewriteRule(rw) => s" ${rw.lhs} --> ${rw.rhs} ";
            case ComposeSeq(s1, s2) => s"$s1;$s2";
            case LeftChoice(s1, s2) => s"$s1<+$s2";
        }

        // def boundVars()
    }
    /*
    case object Var extends StrategyS -> not clear here
    case class NonDetChoice(s1: StrategyS, s2: StrategyS) extends StrategyS
    case class One(s: StrategyS) extends StrategyS
    case class Some(s: StrategyS) extends StrategyS
    case class All(s: StrategyS) extends StrategyS
    case class Rec(x: Var, s: StrategyS) extends StrategyS -> not clear here
    */

    def toStrategyRise(s: StrategyS) : Strategy[Rise] = s match {
        case RewriteRule(rw) => /* t => {
            var eg = EGraph.empty()
            val id = eg.addExpr(Expr.fromNamed(t))
            val searcher = rw.searcher
            val applier = rw.applier
            val shc = SubstsVM // as in Runner, runOne
            searcher.searchEClass(eg, shc, id) match { // i need shc: Substs
                case None => Failure(toStrategyRise(s)); 
                case Some(mat) => {
                    val vec = applier.applyOne(eg, id, shc)(mat.substs(0))
                    /*vec match { // shc
                        case Nil => Failure(toStrategyRise(s));
                        case _ => {
                            val term = Extractor.randomOf(eg,vec(0)) // every cost function should work here because
                                                                    // every eclass should be a singleton
                            val res = Expr.toNamed(ExprWithHashCons.expr(eg)(term))
                            Success(res);
                        }
                    }*/ // i can't match like this because Vec here is defined locally in rise.eqsat and refers to an ArrayBuffer
                    val term = Extractor.randomOf(eg,vec(0)) // every cost function should work here because
                                                                    // every eclass should be a singleton
                    val res = Expr.toNamed(ExprWithHashCons.expr(eg)(term))
                    Success(res);
                    // anyways, an error here would be surprising as we know there is actually something matched
                }
            }
        }*/ ??? ; // the type definition of a rewrite has changed.
        case Skip => id[Rise];
        case Abort => fail[Rise];
        case ComposeSeq(s1, s2) => toStrategyRise(s1) `;` toStrategyRise(s2);
        case LeftChoice(s1, s2) => toStrategyRise(s1) <+ toStrategyRise(s2);
        /* 
        case NonDetChoice(s1, s2) => toStrategyRise(s1) <+> toStrategyRise(s2)
        case One(s) => one(s);
        case Some(s) => some(s);
        case All(s) => all(s);
        */
    }

    // unsure of the type of return here, i think it will be far more difficult than it seems
    // we want to match and apply here
    // : Vec[SearchMatches[shc.Subst]] 
    /*def ematching(eg : EGraph, shc: Substs, s: StrategyS) = s match {
        case RewriteRule(rw) => { 
            val matches = rw.search(eg, shc) 
            val applies = rw.apply(eg, shc)(matches)
        };
        case Skip => ???;
        case Abort => ???;
        case ComposeSeq(s1, s2) => ???;
        case LeftChoice(s1, s2) => ???;
    }
    */
    // could cut the functions in order to apply "one by one"?

   def tolist(shc: Substs)(set: scala.collection.mutable.Set[shc.Subst]) : List[shc.Subst] = 
    {
        var l : List[shc.Subst] = Nil 
        for (beta <- set) {
            l = beta :: l
        }
        l
    }

    def toset(shc: Substs)(list: List[shc.Subst]) : scala.collection.mutable.Set[shc.Subst] = 
    {
        var s : scala.collection.mutable.Set[shc.Subst] = scala.collection.mutable.Set()
        for (beta <- list) {
            s += beta
        }
        s
    }

   def rec_call(eg: EGraph, shc: Substs, pis: List[PatternVarOrNode], tis: List[EClassId])(l: List[shc.Subst]): List[shc.Subst] = 
    (pis, tis) match {
        case (Nil, Nil) => l;
        case (Nil, _) => ???; // just make sure beforehand that the lists have equal length
        case (_, Nil) => ???;
        case (pi::pjs, ti::tjs) => rec_call(eg, shc, pjs, tjs)(ematching_aux(eg,pi,shc,ti)(l));
    }

   
    // i just want a substitution to be a function from variables to eclass ids, e.g. using a hashmap 
   def ematching_aux(eg: EGraph, p: PatternVarOrNode, shc: Substs, t: EClassId)(S: List[shc.Subst]): List[shc.Subst] = // check type
    p match {
        case x: PatternVar => {
            var s : List[shc.Subst] = Nil
            S.foreach{
                case beta => {
                     try { 
                        val v = shc.get(x,beta) // index is in dom(beta)
                        if (eg.find(v) == eg.find(t)) { // find beta(index) = find t
                            s = beta :: s
                        }
                     } catch { // index is not in dom(beta)
                        case _: Throwable => {
                            val id = shc.insert(x,t,beta) // extend beta with index |-> t and add it to s
                            s = beta :: s
                        }
                     } 
                }
            }
            s
        };
        case PatternNode(node) => {
            if (node.childrenCount() == 0) { // node does not have any child
                var s : List[shc.Subst] = Nil
                eg.get(t).nodes.foreach {  // iterate over the class t to see if node belongs to it
                    case n => if (n.matches(node)) {
                        s = S
                    }
                }
                s
            } else { // node has >= 1 children
                var set : scala.collection.mutable.Set[shc.Subst] = scala.collection.mutable.Set() 
                eg.get(t).nodes.foreach { // for every f(t1,...,tn) \in class(t) :
                    case n => if (n.matches(node)) {
                        val pis = node.children().toList.map(x => x.p)
                        val tis = n.children().toList
                        set ++= toset(shc)(rec_call(eg, shc, pis, tis)(S))
                    }
                }
                tolist(shc)(set) // avoid doublons
            }
        };
    }

    def classical_ematching(eg: EGraph, p: PatternVarOrNode) : List[SubstsVM.Subst] = {
        // , shc: Substs
        // union of ematching_aux(eg,p,shc,t)(empty :: Nil) for every eclass t
        val shc = SubstsVM
        var set : scala.collection.mutable.Set[shc.Subst] = scala.collection.mutable.Set()
        val nb_classes = eg.classCount()
        var i = 0
        while (i < nb_classes) {
            set ++= toset(shc)(ematching_aux(eg,p,shc,EClassId(i))(SubstVM.empty :: Nil))
            i += 1
        }
        tolist(shc)(set)
    }
        
    sealed trait STerm 
    case class Ec(i: EClassId) extends STerm
    case class Snode(n: Node[STerm, NatId, DataTypeId, Address]) extends STerm // unsure about the 3 last types

    case class SPair(origin: EClassId, sterm: STerm)

    // caution : using Substitutions instead of Substs might raise problems, the reason of this is the fact that 
    // we store in the substitution the sterms... 


    def stolist(shc: Substitutions)(set: scala.collection.mutable.Set[shc.Substitution]) : List[shc.Substitution] = 
    {
        var l : List[shc.Substitution] = Nil 
        for (beta <- set) {
            l = beta :: l
        }
        l
    }

    def stoset(shc: Substitutions)(list: List[shc.Substitution]) : scala.collection.mutable.Set[shc.Substitution] = 
    {
        var s : scala.collection.mutable.Set[shc.Substitution] = scala.collection.mutable.Set()
        for (beta <- list) {
            s += beta
        }
        s
    }

/*
    def srec_call(eg: EGraph, shc: Substitutions, pis: List[Pattern], tis: List[STerm])(l: List[shc.Substitution]): List[shc.Substitution] = 
    (pis, tis) match {
        case (Nil, Nil) => l;
        case (Nil, _) => ???; // just make sure beforehand that the lists have equal length
        case (_, Nil) => ???;
        case (pi::pjs, ti::tjs) => srec_call(eg, shc, pjs, tjs)(smatching_aux(eg,pi,shc,ti)(l));
    }
*/

    def smatching_aux(eg: EGraph, sg: SGraph, pat: Pattern, shc: Substitutions, t: STerm)(S: List[shc.Substitution]) : List[shc.Substitution] =
    pat.p match { //pat.p
        case x: PatternVar => {
            t match {
                case Ec(i) => {
                    var s : List[shc.Substitution] = Nil
                    S.foreach {
                        case beta => {
                            try { 
                                val v = shc.get(x, beta) // index is in dom(beta)
                                v match {
                                    case Ec(j) => {
                                        if (eg.find(j) == eg.find(i)) { // find beta(index) = find t
                                            s = beta :: s
                                        }
                                    };
                                    case Snode(m) => (); // one is an e-class the other a snode!
                                }
                            } catch { // index is not in dom(beta)
                                case _: Throwable => {
                                    val id = shc.insert(x, Ec(i), beta) // extend beta with index |-> t and add it to s
                                    s = id :: s
                                }
                            } 
                        }
                    }
                    s
                };
                case Snode(n) => {
                    var s : List[shc.Substitution] = Nil
                    S.foreach {
                        case beta => {
                            try {
                                val v = shc.get(x, beta) 
                                v match {
                                    case Ec(j) => (); // one is an e-class the other a snode!
                                    case Snode(m) => {
                                        if (m == n) { // no eclass here, they correspond to the same sterm 
                                                      //iff they are the same
                                            s = beta :: s
                                        }
                                    };
                                }
                            } catch {
                                case _: Throwable => {
                                    val id = shc.insert(x, Snode(n), beta)
                                    s = id :: s
                                }
                            }
                        }
                    }
                    s
                };
            }
        };
        case PatternNode(node) => {
            t match {
                case Ec(i) => {
                    if (node.childrenCount() == 0) { // node does not have any child
                        var s : List[shc.Substitution] = Nil
                        eg.get(i).nodes.foreach {  // iterate over the class i to see if node belongs to it
                            case n => if (n.matches(node)) {
                                s = S
                            }
                        }
                        s
                    } else { // node has >= 1 children
                        var res : List[shc.Substitution] = Nil
                        eg.get(i).nodes.foreach { // for every f(t1,...,tn) \in class(t) :
                            case n => if (n.matches(node)) {
                                val node_terms = node.children().toList 
                                val n_terms = n.children().toList.map(x => Ec(x))
                                /*val node_types = node.types().toList 
                                val n_types = n.types().toList */
                                val node_nats = node.nats().toList 
                                val n_nats = n.nats().toList 
                                val node_dts = node.dataTypes().toList 
                                val n_dts = n.dataTypes().toList 
                                val node_addr = node.addresses().toList 
                                val n_addr = n.addresses().toList 
                                val terms = node_terms.zip(n_terms)
                                //val types = node_types.zip(n_types)
                                val nats = node_nats.zip(n_nats)
                                val dts = node_dts.zip(n_dts)
                                val addr = node_addr.zip(n_addr)
                                val res_terms = terms.foldLeft(S)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_aux(eg, sg, pattern, shc, id)(substs)
                                })
                                //val res_types = types.foldLeft(S)((substs, pair) => pair match {
                                //    case (pattern, id) => smatching_type(eg, sg, pattern, shc, id)(substs)
                                //})
                                val res_nats = nats.foldLeft(res_terms)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_nat(eg, sg, pattern, shc, id)(substs)
                                })
                                val res_data = dts.foldLeft(res_nats)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_data(eg, sg, pattern, shc, id)(substs)
                                })
                                val res_address = addr.foldLeft(res_data)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_address(eg, sg, pattern, shc, id)(substs)
                                })
                                res = stolist(shc)(stoset(shc)(res_address)) // avoid doublons
                            }
                        }
                        res
                    }
                };
                case Snode(n) => {
                    if (node.childrenCount() == 0) { // node does not have any child
                        var s : List[shc.Substitution] = Nil
                        if (n.matches(node)) { // no need to iterate here: only one node in the sterm
                                s = S
                        }
                        s
                    } else { // node has >= 1 children
                        //var set : scala.collection.mutable.Set[shc.Substitution] = scala.collection.mutable.Set() 
                        var res : List[shc.Substitution] = Nil
                        if (n.matches(node)) { // no need to iterate here: only one node in the sterm
                                /*
                                val pis = node.children().toList // .map(x => x.p)
                                val tis = n.children().toList
                                //
                                set = stoset(shc)(srec_call(eg, shc, pis, tis)(S)) // i must change rec_call
                                */
                                val node_terms = node.children().toList 
                                val n_terms = n.children().toList //.map(x => Ec(x))
                                //val node_types = node.types().toList 
                                //val n_types = n.types().toList 
                                val node_nats = node.nats().toList 
                                val n_nats = n.nats().toList 
                                val node_dts = node.dataTypes().toList 
                                val n_dts = n.dataTypes().toList 
                                val node_addr = node.addresses().toList 
                                val n_addr = n.addresses().toList 
                                val terms = node_terms.zip(n_terms)
                                //val types = node_types.zip(n_types)
                                val nats = node_nats.zip(n_nats)
                                val dts = node_dts.zip(n_dts)
                                val addr = node_addr.zip(n_addr)
                                val res_terms = terms.foldLeft(S)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_aux(eg, sg, pattern, shc, id)(substs)
                                })
                                //val res_types = types.foldLeft(res_terms)((substs, pair) => pair match {
                                //    case (pattern, id) => smatching_type(eg, sg, pattern, shc, id)(substs)
                                //})
                                val res_nats = nats.foldLeft(res_terms)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_nat(eg, sg, pattern, shc, id)(substs)
                                })
                                val res_data = dts.foldLeft(res_nats)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_data(eg, sg, pattern, shc, id)(substs)
                                })
                                val res_address = addr.foldLeft(res_data)((substs, pair) => pair match {
                                    case (pattern, id) => smatching_address(eg, sg, pattern, shc, id)(substs)
                                })
                                res = stolist(shc)(stoset(shc)(res_address)) // avoid doublons
                        }
                        res 
                    }
                };
            }
        };
    }

    // eclasses have a typeId !

    def smatching_nat(eg: EGraph, sg: SGraph, pat: NatPattern, shc: Substitutions, dt: NatId)(S: List[shc.Substitution]) : List[shc.Substitution] =
        S // TO MODIFY

    def smatching_data(eg: EGraph, sg: SGraph, pat: DataTypePattern, shc: Substitutions, dt: DataTypeId)(S: List[shc.Substitution]) : List[shc.Substitution] = {
    pat match {
        case w: DataTypePatternVar => {
            var s : List[shc.Substitution] = Nil
            S.foreach {
                case beta => {
                    try { 
                        val v = shc.get(w, beta) // index is in dom(beta)
                        // val id = sg.add_children(dt)
                        if (v == dt) {
                            s = beta :: s 
                        }
                    } catch { // index is not in dom(beta)
                        case _: Throwable => {
                            val id = shc.insert(w, dt, beta) // extend beta with index |-> t and add it to s 
                            // sg.add_children(dt)
                            s = id :: s
                        }
                    }
                };
            }
            s
        };
        case DataTypePatternNode(n) => {
            var res : List[shc.Substitution] = Nil
            val node = sg.apply(dt)
            if (n.matches(node)) {
                val n_nats = n.nats().toList
                val n_dt = n.dataTypes().toList 
                val node_nats = node.nats().toList 
                val node_dt = node.dataTypes().toList
                val nats = n_nats.zip(node_nats)
                val dts = n_dt.zip(node_dt)
                val res_nat =  nats.foldLeft(S)((substs, pair) => pair match {
                    case (pattern, id) => smatching_nat(eg, sg, pattern, shc, id)(substs)
                }) // smatching_nat(eg, n.nats(), shc, node_nats)
                val res_data = dts.foldLeft(res_nat)((substs, pair) => pair match {
                    case (pattern, id) => smatching_data(eg, sg, pattern, shc, id)(substs)
                })
                res = stolist(shc)(stoset(shc)(res_data)) // avoid doublons
            }
            res
        };
        case DataTypePatternAny => S;
    }
    }

    def smatching_type(eg: EGraph, sg: SGraph, pat: TypePattern, shc: Substitutions, t: TypeId)(S: List[shc.Substitution]) : List[shc.Substitution] = pat match {
        case w : TypePatternVar => {
            var s : List[shc.Substitution] = Nil
            S.foreach {
                case beta => {
                    try { 
                        val v = shc.get(w, beta) // index is in dom(beta)
                        // val id = sg.add_children(dt)
                        if (v == t) {
                            s = beta :: s 
                        }
                    } catch { // index is not in dom(beta)
                        case _: Throwable => {
                            val id = shc.insert(w, t, beta) // extend beta with index |-> t and add it to s 
                            // sg.add_children(dt)
                            s = id :: s
                        }
                    }
                };
            }
            s
        };
        case TypePatternNode(n) => {
            var res : List[shc.Substitution] = Nil
            val node = sg.apply(t)
            if (n.matches(node)) {
                val n_types = n.types().toList 
                val node_types = node.types().toList 
                val n_nats = n.nats().toList 
                val node_nats = node.nats().toList 
                val n_dts = n.dataTypes().toList 
                val node_dts = node.dataTypes().toList 
                val types = n_types.zip(node_types)
                val nats = n_nats.zip(node_nats)
                val dts = n_dts.zip(node_dts)
                val res_types = types.foldLeft(S)((substs, pair) => pair match {
                    case (pattern, id) => smatching_type(eg, sg, pattern, shc, id)(substs)
                })
                val res_nats = nats.foldLeft(res_types)((substs, pair) => pair match {
                    case (pattern, id) => smatching_nat(eg, sg, pattern, shc, id)(substs)
                })
                val res_data = dts.foldLeft(res_nats)((substs, pair) => pair match {
                    case (pattern, id) => smatching_data(eg, sg, pattern, shc, id)(substs)
                })
                res = stolist(shc)(stoset(shc)(res_data)) // avoid doublons
            }
            res
        };
        case TypePatternAny => S;
        case dt: DataTypePattern => smatching_data(eg, sg, dt, shc, t.asInstanceOf[DataTypeId])(S);
    }

    def smatching_address(eg: EGraph, sg: SGraph, pat: AddressPattern, shc: Substitutions, t: Address)(S: List[shc.Substitution]) : List[shc.Substitution] =
        S // TO MODIFY

    case class SMatches(spair: SPair, substs: List[SubstitutionsVM.Substitution])

    def treat_worklist(eg: EGraph, sg: SGraph, p: Pattern, worklist: List[SPair], aux: List[SMatches]) : List[SMatches] = {
        val shc = SubstitutionsVM
        worklist match {
            case Nil => aux;
            case head :: next => {
                val substs = (smatching_aux(eg, sg, p, shc, head.sterm)(SubstitutionVM.empty :: Nil))
                if (substs != Nil) {
                    treat_worklist(eg, sg, p, next, SMatches(head,substs)::aux)
                } else { // if we don't match any substitution, why bother?
                    treat_worklist(eg, sg, p, next, aux)
                }
            };
                //treat_worklist(eg, p, next, aux ::: (smatching_aux(eg, p, shc, head.sterm)(SubstitutionVM.empty :: Nil)));
        }
    }

    def classical_smatching(eg: EGraph, sg: SGraph, p: Pattern, worklist: List[SPair]) : List[SMatches] = {
        treat_worklist(eg, sg, p, worklist, Nil)
    }

    def delta_lists(l1: List[SPair], l2: List[SPair]) : List[SPair] = 
    // this function should only be called with l2 a sublist of l1, with the same order of elements
    (l1, l2) match {
        case (Nil, _) => Nil;
        case (_, Nil) => l1;
        case (h1 :: t1, h2 :: t2) => {
            if (h1 == h2) {
                delta_lists(t1,t2)
            } else {
                h1 :: (delta_lists(t1, t2))
            }
        }
    }

    
    def s_apply_one(sg: SGraph, pattern: Pattern, subst: SubstitutionsVM.Substitution, new_wl: List[STerm]) : List[STerm] = {
        val shc = SubstitutionsVM
        def missingRhsTy[T](): T = throw new Exception("unknown type on right-hand side")
        def pat1(pat: Pattern): List[STerm] = {
            pat.p match {
            case w: PatternVar => shc.get(w, subst)::new_wl
            case PatternNode(n) => {
                /*val enode = n.map(pat, nat, data, addr)
                egraph.add(enode, `type`(p.t)) */
                val snode = Snode(n.map(pat2, nat, data, addr))
                sg.set_type_of(snode, `type`(pat.t))
                snode::new_wl
            }
            }
        }
        def pat2(pat: Pattern): STerm = {
            pat.p match {
                case w: PatternVar => shc.get(w, subst)
                case PatternNode(n) => {
                    /*val enode = n.map(pat, nat, data, addr)
                    egraph.add(enode, `type`(p.t)) */
                    val snode = Snode(n.map(pat2, nat, data, addr))
                    sg.set_type_of(snode, `type`(pat.t))
                    snode
                }
            }
        }
        def nat(p: NatPattern): NatId = {
            p match {
            case w: NatPatternVar => shc.get(w, subst)
            case NatPatternNode(n) => sg.add(n.map(nat)) 
            case NatPatternAny => missingRhsTy()
            }
        }
        def data(pat: DataTypePattern): DataTypeId = {
            pat match {
            case w: DataTypePatternVar => shc.get(w, subst)
            case DataTypePatternNode(n) => sg.add(n.map(nat, data)) 
            case DataTypePatternAny => missingRhsTy()
            }
        }
        def `type`(pat: TypePattern): TypeId = {
            pat match {
            case w: TypePatternVar => shc.get(w, subst)
            case TypePatternNode(n) => sg.add(n.map(`type`, nat, data))
            case TypePatternAny => missingRhsTy()
            case dtp: DataTypePattern => data(dtp)
            }
        }
        def addr(pat: AddressPattern): Address = {
            pat match {
            case w: AddressPatternVar => shc.get(w, subst)
            case AddressPatternNode(n) => n
            case AddressPatternAny => missingRhsTy()
            }
        }

        pat1(pattern)
    }

    def s_apply_all(sg: SGraph, pattern: Pattern, matches: List[SMatches]) : List[SPair] = matches match {
        case Nil => Nil;
        case head :: next => {
            val origin = head.spair.origin 
            // val sterm = head.spair.sterm 
            val substs = head.substs 
            var applied_all_substs : List[STerm] = Nil
            for (sigma <- substs) {
                print(s"\n start apply $sigma \n") // sigma is empty for the moment...
                applied_all_substs = s_apply_one(sg, pattern, sigma, applied_all_substs)
                print("\n end apply \n")
            };
            val new_spairs = applied_all_substs.map(sterm => SPair(origin, sterm))
            new_spairs ::: (s_apply_all(sg, pattern, next))
        };
    }

    def s_apply_aux(eg: EGraph, sg: SGraph, s: StrategyS, worklist: List[SPair]) : List[SPair] = s match {
        case Skip => worklist;
        case Abort => Nil;
        case RewriteRule(rw) => {
            val lhs = rw.lhs
            val rhs = rw.rhs
            print(s"\n lhs pattern: ${lhs.p} \n")
            print(s"\n lhs type: ${lhs.t} \n")
            print(s"\n rhs pattern: ${rhs.p} \n")
            print(s"\n rhs type: ${rhs.t} \n")
            val matches = classical_smatching(eg, sg, lhs, worklist)
            print(s"\n nb matches: ${matches.size} \n")
            s_apply_all(sg, rhs, matches)
        };
        case ComposeSeq(s1, s2) => s_apply_aux(eg, sg, s2, s_apply_aux(eg, sg, s1, worklist));
        case LeftChoice(s1, s2) => {
            val l1 = s_apply_aux(eg, sg, s1, worklist)
            val worklist2 = delta_lists(worklist, l1)
            val l2 = s_apply_aux(eg, sg, s2, worklist2)
            l1 ::: l2
        };
    }

    def listToVec[A](l : List[A]) : Vec[A] = {
        var vec : Vec[A] = Vec.empty[A]
        l.foreach(el => vec += el)
        vec
    }

    def s_add(eg: EGraph, sg: SGraph, roots: List[SPair]) : Vec[EClassId] = {
        var memo: HashMap[STerm, EClassId] = HashMap.empty

        def s_add_one(sterm : STerm) : EClassId = sterm match {
            case Ec(i) => eg.find(i); // representant of the eclass
            case Snode(n) => {
                /*
                val enode = n.mapChildren(child => sg.get_type_of(child) match {
                    case None => ???; // should not happen
                    case Some(t) => s_add_one(child, t)
                })
                eg.add(enode, t) */
                memo.get(sterm) match {
                    case None => {
                        val enode = n.mapChildren(s_add_one)
                        sg.get_type_of(sterm) match {
                            case None => ???; // should not happen
                            case Some(t) => {
                                val id = eg.add(enode, t)
                                memo += sterm -> id 
                                id
                            };
                        }
                    };
                    case Some(id) => id;
                }
            };
        }

        // roots.map(pair => s_add_one(pair.sterm))

        def unions(spair: SPair) : (EClassId, Boolean) = {
            val eid = s_add_one(spair.sterm) 
            eg.union(eid, spair.origin)
        }
        //var added = Vec.empty[EClassId]
        val unified = roots.map(pair => unions(pair))
        val filtered = unified.filter({ case (id, bool) => bool})
        listToVec[EClassId](filtered.map({case (id, bool) => id}))
    }

    def s_apply(eg: EGraph, s: StrategyS) : Vec[EClassId] = {
        val worklist = eg.classes.map{case (index, eclass) => (index, Ec(index))}.toList.map{case (x,y) => SPair(x,y)} 
        // it is bad,
        // i do it for every eclassid instead of just choosing one eclassid per eclass!
        val sg = SGraph.empty()
        // instead of an empty sgraph, i must have a copy of the hashconses from the egraph (as well as the types?)
        val endlist = s_apply_aux(eg, sg, s, worklist)
        // starting from endlist, determine which enodes should be added to the egraph
        // & add them bottom-up for efficiency reasons
        s_add(eg, sg, endlist)
    }
}