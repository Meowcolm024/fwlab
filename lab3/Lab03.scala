import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*


object Lab03 extends lisa.Main{

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val Q = SchematicPredicateLabel("P", 1)
  private val H = SchematicPredicateLabel("R", 2)

  ///////////////////////
  // First Order Logic //
  ///////////////////////


  // you may need to use the following proof tactics:
  // have("_____ |- _____") by Restate
  // have("_____ |- _____") by Trivial
  // have("_____ |- _____") by Weakening     (Restate and Weakening can replace all single-premise Sequent Calculus proof steps. Try them before using Trivial.)
  // have("_____ |- _____") by LeftForall(term)(premise)
  // have("_____ |- _____") by RightForall(premise)
  // have("_____ |- _____") by LeftExists(premise)
  // have("_____ |- _____") by RightExists(term)
  // have("_____ |- _____") by InstantiateForall(term*)(premise)
  // have("_____ |- _____") by LeftOr(premise1, premise2)
  // have("_____ |- _____") by LeftImplies(premise1, premise2)
  // have("_____ |- _____") by RightIff(premise1, premise2)
  // have("_____ |- _____") by RightAnd(premise1, premise2)
  // have("_____ |- _____") by Cut(premise1, premise2)
  // andThen(applySubst(P <=> Q))      (replaces instances of P by instances of Q in the current sequent)
  // andThen(applySubst(x = y))        (replaces instances of x by instances of y in the current sequent)
  //
  // andThen("_____ |- _____") by Tactic    may be use instead of "have" and (premise). In that case, the premise is replaced by the previously proven step.
  //
  //Details about Sequent Calculus in LISA can be found here: https://github.com/epfl-lara/lisa/blob/main/Reference%20Manual/lisa.pdf

  THEOREM("Ex_All_implies_All_Ex") of "∃'x. ∀'y. 'R('x, 'y) ⊢ ∀'y. ∃'x. 'R('x, 'y)" PROOF {
    have ( H(x, y) |- H(x, y) ) by Hypothesis  // start
    andThen ( forall(y, H(x, y)) |- H(x, y) ) by LeftForall(y)
    andThen ( forall(y, H(x, y)) |- exists(x, H(x, y)) ) by RightExists(x)
    andThen ( exists(x, forall(y, H(x, y))) |- exists(x, H(x, y)) ) by LeftExists
    andThen ( exists(x, forall(y, H(x, y))) |- forall(y, exists(x, H(x, y))) ) by RightForall
    // showCurrentProof()
  }

  THEOREM("Unique_Exist_Variant") of "∃'y. ∀'x. ('P('x) ⇔ 'x='y) ⊢ ∃'y. 'P('y) ∧ (∀'x. 'P('x) ⇒ 'x='y)" PROOF {
    // exist y, all x, (P(x) <=> x=y) |- 
    //    exist y, P(y) /\ (all x, P(x) => (x=y))

    assume(exists(y, forall(x, Q(x) <=> (x===y) )))

    have(forall(x, Q(x) ==> (x===y)) |- forall(x, (Q(x) ==> (x===y)))) by Restate
    val p1 = andThen(forall(x, Q(x) <=> (x===y)) |- forall(x, (Q(x) ==> (x===y)))) by Weakening
    have(forall(x, Q(x)) |- forall(x, Q(x))) by Restate
    have(forall(x, Q(x) <=> (x===y)) |- Q(x)) by Trivial
    andThen(applySubst(x === y))
    val p2 = have(forall(x, Q(x) <=> (x===y)) |- Q(y)) by Restate
    have(forall(x, Q(x) <=> (x===y)) |- Q(y) /\ forall(x, Q(x) ==> (x===y))) by RightAnd(p1, p2)
    andThen(exists(y, forall(x, Q(x) <=> (x===y))) |- Q(y) /\ forall(x, Q(x) ==> (x===y))) by LeftExists
    andThen(exists(y, forall(x, Q(x) <=> (x===y))) |- exists(y, Q(y) /\ forall(x, Q(x) ==> (x===y)))) by RightExists(y)
    //have(exists(y, forall(x, Q(x) <=> (x===y))) |- exists(y, Q(y) /\ forall(x, Q(x) ==> (x===y)))) by Trivial

  }



  ////////////////
  // Set Theory //
  ////////////////


  //This one is given as an example
  THEOREM("Subset_Reflexivity") of " ⊢ subset_of('x, 'x)" PROOF {
    val subs = have(subsetAxiom) //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x = 'y
    showCurrentProof()               //shows the current sequent calculus proof
    val r1 = andThen(() |- forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)) by InstantiateForall(x, x)    //InstantiateForall will instantiate a universally bound formula on the right of a sequent with the given terms.
    have(() |- in(z, x) ==> in(z, x)) by Restate                                                            //Restate solves automatically a class of easy proposition, including reflexivity of equality, alpha-equivalence of formulas, and some propositional logic properties
    andThen(() |- forall(z, in(z, x) ==> in(z, x))) by RightForall
    andThen(applySubst(forall(z, in(z, x) ==> in(z, x)) <=> subset(x, x)))                                  //applySubst will replace  occurences of the left-hand-side of the equivalence given in argument by the right-hand-side in the current sequent.
    Discharge(r1)                                                                                           //Discharge removes the formula proven on the right of sequent r1 from the left-hand-side of the current sequent
  }

  THEOREM("Subset_Transitivity") of "subset_of('x, 'y); subset_of('y, 'z) ⊢ subset_of('x, 'z)" PROOF {
    val subs = have(subsetAxiom)          //  ⊢ ∀'x. ∀'y. 'x ⊆ 'y ⇔ (∀'z. 'z ∊ 'x ⇒ 'z ∊ 'y)
    val a = VariableLabel("a")
    val r1 = have(() |- forall(a, in(a, x) ==> in(a, y)) <=> subset(x, y) ) by InstantiateForall(x, y)(subsetAxiom)
    val r2 = have(() |- forall(a, in(a, y) ==> in(a, z)) <=> subset(y, z) ) by InstantiateForall(y, z)(subsetAxiom)
    val r3 = have(() |- forall(a, in(a, x) ==> in(a, z)) <=> subset(x, z) ) by InstantiateForall(x, z)(subsetAxiom)
    have( (in(a, x) ==> in(a, y), in(a, y) ==> in(a, z) ) |- in(a, x) ==> in(a, z) ) by Trivial
    andThen( (forall(a, in(a, x) ==> in(a, y)) , in(a, y) ==> in(a, z) ) |- in(a, x) ==> in(a, z) ) by LeftForall(a)
    andThen( (forall(a, in(a, x) ==> in(a, y)) , forall(a, in(a, y) ==> in(a, z)) ) |- in(a, x) ==> in(a, z) ) by LeftForall(a)
    andThen( (forall(a, in(a, x) ==> in(a, y)) , forall(a, in(a, y) ==> in(a, z)) ) |- forall(a, in(a, x) ==> in(a, z)) ) by RightForall
    andThen( applySubst( forall(a, in(a, x) ==> in(a, y)) <=> subset(x, y)) )
    andThen( applySubst( forall(a, in(a, y) ==> in(a, z)) <=> subset(y, z)) )
    andThen( applySubst( forall(a, in(a, x) ==> in(a, z)) <=> subset(x, z)) )
    Discharge(r1)
    Discharge(r2)
    Discharge(r3)
    // showCurrentProof()
  }

  THEOREM("Subset_Antisymmetry") of "subset_of('x, 'y); subset_of('y, 'x)  ⊢ 'x='y " PROOF {
    val ext = have(extensionalityAxiom)    //  ⊢ ∀'x. ∀'y. (∀'z. 'z ∊ 'x ⇔ 'z ∊ 'y) ⇔ 'x = 'y
    val subs = have(subsetAxiom)           //  ⊢ ∀'x. ∀'y. 'x ⊆ 'y ⇔ (∀'z. 'z ∊ 'x ⇒ 'z ∊ 'y)
    val r1 = have(() |- forall(z, in(z, x) <=> in(z, y)) <=> (x === y)) by InstantiateForall(x, y)(extensionalityAxiom)
    val r2 = have(() |- forall(z, in(z, x) ==> in(z, y)) <=> subset(x, y) ) by InstantiateForall(x, y)(subsetAxiom)
    val r3 = have(() |- forall(z, in(z, y) ==> in(z, x)) <=> subset(y, x) ) by InstantiateForall(y, x)(subsetAxiom)
    have( (in(z, x) ==> in(z, y), in(z, y) ==> in(z, x)) |- in(z, x) <=> in(z, y) ) by Trivial
    andThen( (forall(z, in(z, x) ==> in(z, y)), in(z, y) ==> in(z, x)) |- in(z, x) <=> in(z, y)) by LeftForall(z)
    andThen( (forall(z, in(z, x) ==> in(z, y)), forall(z, in(z, y) ==> in(z, x))) |- in(z, x) <=> in(z, y)) by LeftForall(z)
    andThen( (forall(z, in(z, x) ==> in(z, y)), forall(z, in(z, y) ==> in(z, x))) |- forall(z, in(z, x) <=> in(z, y))) by RightForall
    andThen( applySubst(forall(z, in(z, x) <=> in(z, y)) <=> (x === y)) )
    andThen( applySubst(forall(z, in(z, x) ==> in(z, y)) <=> subset(x, y)) )
    andThen( applySubst(forall(z, in(z, y) ==> in(z, x)) <=> subset(y, x)) )
    Discharge(r1)
    Discharge(r2)
    Discharge(r3)
    // showCurrentProof()
  }


}
