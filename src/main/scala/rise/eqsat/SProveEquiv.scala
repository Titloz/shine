package rise.eqsat

import scala.language.implicitConversions

case object SCouldNotProveEquiv extends Exception

object SProveEquiv {
   def init(): SProveEquiv = new SProveEquiv(
    filter = NoPredicate(),
    transformRunner = r => r,
    endStrategies = Seq(),
    bidirectionalSearch = false,
  )

  case class OneOrMore[T](seq: Seq[T])

  object syntax {
    implicit def one[T](t: T): OneOrMore[T] = OneOrMore(Seq(t))
    implicit def more[T](s: Seq[T]): OneOrMore[T] = OneOrMore(s)
  }
}

class SProveEquiv(
  var filter: Predicate,
  var transformRunner: Runner => Runner,
  var endStrategies: Seq[ElevateEqsat.NamedStrategyS],
  var bidirectionalSearch: Boolean,
) {
  import SProveEquiv._

  def withFilter(filter: Predicate): SProveEquiv = {
    this.filter = filter
    this
  }

  def withRunnerTransform(f: Runner => Runner): SProveEquiv = {
    transformRunner = f
    this
  }

  def bidirectional(): SProveEquiv = {
    bidirectionalSearch = true
    this
  }

  def withEndRules(rs: Seq[ElevateEqsat.NamedStrategyS]): SProveEquiv = {
    endStrategies = rs
    this
  }

  def runBENF(starts: OneOrMore[rise.core.Expr],
              goals: OneOrMore[rise.core.Expr],
              strategies: Seq[ElevateEqsat.NamedStrategyS]): Unit = {
    val normStarts = starts.seq.map(s => BENF.normalize(Expr.fromNamed(s)))
    val normGoals = goals.seq.map(g => BENF.normalize(Expr.fromNamed(g)))
    for ((start, i) <- normStarts.zipWithIndex) {
      println(s"normalized start n°$i: ${Expr.toNamed(start)}")
    }
    for ((goal, i) <- normGoals.zipWithIndex) {
      println(s"normalized goal n°$i: ${Expr.toNamed(goal)}")
    }
    run(OneOrMore(normStarts), OneOrMore(normGoals), strategies)
  }

  def runCNF(starts: OneOrMore[rise.core.Expr],
             goals: OneOrMore[rise.core.Expr],
             strategies: Seq[ElevateEqsat.NamedStrategyS]): Unit = {
    val normStarts = starts.seq.map(s => CNF(Expr.fromNamed(s)))
    val normGoals = goals.seq.map(g => CNF(Expr.fromNamed(g)))
    for ((start, i) <- normStarts.zipWithIndex) {
      println(s"normalized start n°$i: ${Expr.toNamed(start)}")
    }
    for ((goal, i) <- normGoals.zipWithIndex) {
      println(s"normalized goal n°$i: ${Expr.toNamed(goal)}")
    }
    run(OneOrMore(normStarts), OneOrMore(normGoals), strategies)
  }

  def run(starts: OneOrMore[Expr],
          goals: OneOrMore[Expr],
          strategies: Seq[ElevateEqsat.NamedStrategyS]): Unit = {
    val egraph = EGraph.empty()
    egraph.requireAnalyses(filter.requiredAnalyses())
    val startId = starts.seq.tail.foldLeft(egraph.addExpr(starts.seq.head)) { case (id, e) =>
      egraph.union(id, egraph.addExpr(e))._1
    }

    if (bidirectionalSearch) {
      runBidirectional(egraph, startId, goals.seq, strategies)
    } else {
      runUnidirectional(egraph, startId, goals.seq, strategies)
    }
  }

  private def runUnidirectional(egraph: EGraph,
                                startId: EClassId,
                                goals: Seq[Expr],
                                strategies: Seq[ElevateEqsat.NamedStrategyS]): Unit = {
    var remainingGoals = goals

    def goalReached(g: Expr): Boolean =
      egraph.lookupExpr(g).contains(egraph.find(startId))
    val runner = transformRunner(Runner.init()).doneWhen { r =>
      util.printTime("goal check", {
        remainingGoals = remainingGoals.filterNot(goalReached)
        remainingGoals.isEmpty
      })
    }.srun(egraph, filter, strategies, Seq(startId))
    afterRun(runner, egraph, startId, goals, i => goalReached(goals(i)))
  }

  private def runBidirectional(egraph: EGraph,
                               startId: EClassId,
                               goals: Seq[Expr],
                               strategies: Seq[ElevateEqsat.NamedStrategyS]): Unit = {
    val goalIds = goals.map(egraph.addExpr)
    val runner = transformRunner(Runner.init()).doneWhen { _ =>
      goalIds.forall(g => egraph.findMut(startId) == egraph.findMut(g))
    }.srun(egraph, filter, strategies, startId +: goalIds)
    afterRun(runner, egraph, startId, goals, {
      i => egraph.findMut(startId) == egraph.findMut(goalIds(i))
    })

    goals.foreach { g =>
      assert(egraph.lookupExpr(g).contains(egraph.find(startId)))
    }
  }

  private def afterRun(runner: Runner,
                       egraph: EGraph,
                       startId: EClassId,
                       goals: Seq[Expr],
                       goalReached: Int => Boolean): Unit = {
    runner.printReport()

    // egraph.dot().toSVG("/tmp/e-graph.svg")
    if (!runner.stopReasons.contains(Done)) {
      runner.iterations.foreach(println)
      val (found, notFound) = goals.indices.partition(goalReached)

      val idsToFind = notFound.map(i => egraph.addExpr(goals(i)))
      val endRunner = Runner.init().doneWhen { _ =>
        idsToFind.forall(id => egraph.findMut(startId) == egraph.findMut(id))
      }.srun(egraph, NoPredicate(), endStrategies, Seq(startId))
      if (endRunner.stopReasons.contains(Done)) {
        return
      }
      
      println(s"found: ${found.mkString(", ")}")
      val (endFound, neverFound) = notFound.zip(idsToFind).partition { case (_, id) =>
        egraph.findMut(startId) == egraph.findMut(id)
      }
      println(s"found at the end: ${endFound.map(_._1).mkString(", ")}")
      println(s"never found: ${neverFound.map(_._1).mkString(", ")}")
      throw SCouldNotProveEquiv
    }
  }
}
