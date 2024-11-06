(* ------------- First things first ... What is *Induction*? ----------------------------------*)

(* Induction is the principle of concluding a general thing (theory/hypothesis/fact) from examples.
   Like apples, pears, and melons are examples of the concept fruit.

   Inductive datatypes are hence inductive because you define them by giving all the instances that could make up a member of that type and "conclude" the type. from the definition coq concludes (because it requries this) that
      - those constructors are the only ways to build the type
      - you can build any of the recursive instances based on non-recursive instances of the
      type 
   
   Inductive types can be recursive, but they do not have to.
   In coq they are really types that are 'induced' by new constructors ... Everything else (like the lemmata,  function types and definitions is giving names to specializations of generic types)
*)

Inductive  someInductive : Type := SomeConstructor (x: nat) | OtherConstructor (b: bool).

Definition justAnInstanceOfListA := list nat. 
Fixpoint justAnInstanceOfAtoB (a : nat) : someInductive := 
   match a with 
   | 0 => SomeConstructor a 
   | S n => justAnInstanceOfAtoB n 
   end.


(* Let's have an inductive type that is recursive (because those are the only ones you need 
  [induction] for when you want to proof something about them)*)

Inductive exampleType : Set := 
 | BaseE (n : nat)
 | StepE (n : nat) (innerE: exampleType)
.

(*
 Given this definition, coq derives *induction principles* to reason about the type.
 Namely: 
   exampleType_ind
   exampleType_rect
   exampleType_rec
   exampleType_sind
*)

Print exampleType_ind.



(* What does it say? Essentially it's a function that takes 3 arguments:
    1.  a predicate P that maps elements of exampleType to property 
        P: exampleType -> Prop  ... meaning it may or may not hold
    2.  a function f that gives you P (BaseE n) for all n
        meaning you proof P holds for the base elements
    3.  a function f0 that gives you P (StepE ... ) if you give it a P innerE
  
   and then combines f and f0 to a fixpoint (recursive) 
   function that gives you P e for any element e of exampleType
   
*)


(* All four induction principles follow this pattern. The only difference is, 
   that _ind works on inductive proofs i.e. mappings from elements of exampleType to 
   properties (forall P: exampleType → Prop), while 
   _rec, _rect and _sind generalize the mapping to 
     another Set (_rec:  forall P: exampleType → Set),
     another Type  (_rect: forall P: exampleType → Type), 
     and an SProp (_sind: forall P: exampleType → SProp)
*)

Print exampleType_rec.
Print exampleType_rect.
Print exampleType_sind.

(* For comparison, let's look at a type with more than one 'basic' constructor*)
Inductive exampleType2 : Set := 
 | Base1E (n : nat)
 | Base2E (n: nat)
 | SteppE (n : nat) (innerE: exampleType)
.

(* 
   Here you can see that the induction principle looks pretty 
   similar, but you have to provide one function for each of the
   base constructors
*)
Print exampleType2_ind.


(*
Now we can use this priciples to do "poof by induction". The general idea is 

1. You have an inductive type T and a property P you want to proof for every element t:T of that type

2. You proof that the property of interest holds for all the "basic" elements.

3. You proof that, for all the non-basic i.e. recursive elements of the type, the property will hold for the new one if 
   holds for the inner/smaller/basic one. Assuming that P hold for the inner elements is the induction hypothesis.

4. Since the basic elements fulfill the property and every building step you can make preserves the property
   the property holds for everything you can build. 

So let's look at an example
*)

Fixpoint sum_example (e: exampleType) : nat := 
 match e with 
 | BaseE n => n
 | StepE n innerE => n + sum_example innerE
 end.


(* 
Let's do an inductive proof using the induction principle directly*)
Lemma sum_bigger_0 : forall e:exampleType, sum_example e >= 0.
Proof.
    apply exampleType_ind.
    (*applying the induction hypothesis directly gives you backward reasoning i.e. 
      1. it matches the conclusion/return term of the induction principle with
      the goal .. that's how it figures out P
      2. it replaces the original goal with the 'input function' of the induction
         principle i.e. the function to proof P for the base element and
         the function to proof P for the step 
      *)
   - intro n.
     apply le_0_n.
   - intros n innerE IH.
     (* Now we introduced the induction hypothesis by hand and are essentially
        at the same point as we'd been using the induction tactic *)
     apply le_0_n. 
Qed. 
 
 
(*------------------- The induction tactic -----------------------*)

(*The [induction] tactic will do the same steps we did by hand just now
   - apply the induction principle for the term we do induction on
   - for each constructor of the terms type -> generate a subgoal (to provide the 
      constructor -> Prop function)
   - introduce the arguments of the constructors
   - for recursive constructors also introduce the induction hypothesis 
*)

Lemma sum_bigger_0' : forall e:exampleType, sum_example e >= 0.
Proof.
   induction e.
   - apply le_0_n.
   - apply le_0_n. 
Qed. 

(* Knowing that the induction tactic will introduce 
   - a case for all constructors of the term
   - the parameters of the respective constructors and
   - an induction hypothesis for each nested constructor
    it is possible to name them in the call to the induction tactic using the usual intro patterns
  e.g. exampleType has two constructors, one of them will also generate an induction hypothesis 
  so we can use a two branched disjunction pattern like this 
*)


Lemma sum_bigger_0'' : forall e: exampleType, sum_example e >= 0.
Proof.
   induction e as [ nBase | nStep innerE IHinnerE ].
   - apply le_0_n.
   - apply le_0_n. 
Qed. 


(*------------------------ The Coq induction tactic (details) -----------------------------------*)

(*

General syntax (documented at: https://coq.inria.fr/doc/V8.18.0/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.induction): 

   induction induction_clause+, induction_principle
   -> meaning you can call the induction tactic with a comma separated list of induction clauses and an induction
      principle

   induction_clause := induction_arg as or_and_intropattern  eqn:naming_intropattern* occurrences  
   
      induction_arg -> name or number of the term to do induction on 
      or_and_intropattern -> intropattern to name things e.g. induction n as [firstArg | secondArg IH]
      eqn:naming_intropattern -> to keep the current constructor in the context, give it a name with naming_intropattern
      occurrences -> induction n in someterm  

   induction_principle -> the induction principle you want to use preceded by the "using" keyword e.g.
                          induction n using nat_ind.

   Next we'll have a look at how to use the syntax. 
*)

(*
   We don't care too much about the actual proof, but more about the ways
   you can apply the induction tactic here.
*)

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* Coq will automatically chose exampleType_ind as the induction principle 
     and name the parameters and induction hypothesis*)
  intros e1 e2. induction e1.
Abort.

(*This is really nothing else, than using the (implicitly) given induction principle, 
  mapping it to the constructors of your goal and generate a proof goal for each constructor + 
  induction hypotheses. 
  That's why a third way of achieving the same this is to use the destruct tactic with an induction principle.
  Destruting itself would just generate subgoals for each constructor, adding the induction principle
  introduces the assumptions about the base/child cases as IH along *)

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* Coq will automatically choose exampleType_ind as the induction principle 
     and name the parameters and induction hypothesis*)
  intros e1 e2. destruct e1 using exampleType_ind.
Abort.



Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* in fact you don't need to introduce premises that occur before the term you do induction on. This will happen automatically.
  Here e1 is introduced because it occurred before e2.
   *)
  induction e2.
Abort.

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* In some cases it is helpful to have a more general induction hypothesis
     For instance, in the previous example you got 
     IHe2 : sum_example e1 = sum_example e2 
     meaning for a specific e1 and e2 it holds that sum_example e1 = sum_example e2
     
     Now, we always need to introduce premises up to the term we do induction on.
     But we can get a more general/stronger induction hypothesis by removing
     premises, in this case the specific e1 from the context again.
   *)
  intros e1 e2.
  revert e1.
  induction e2.
Abort.


Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* 
     If you need/want to do induction on more than one term 
     you can list them this way. 
     The induction principle will be the same for all of them 
     and you will get a nested induction.
   *)
  induction e1, e2.
Abort.

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* 
     This is equivalent to the version above, i.e. you do the nested 
     induction by hand.
   *)
  induction e1.
  - induction e2. admit. admit.
  - induction e2.  
Abort.



Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* 
    Obviously, things become more readable, when you name the introduced hypothesis'.
   *)
  induction e1 as [nBase | nStep innerE IHinnerE].
Abort.

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
  (* 
    Remember that induction will generate a subgoal for each constructor of your
    term. Instead of just introducing the parameters of those constructors, you can also
    keep the constructor itself in scope. 
   *)
  induction e1 as [nBase | nStep innerE IHinnerE] eqn:CurrentE1.
Abort.

Lemma sum_nonsense : forall e1 e2 : exampleType,
  sum_example e1 = sum_example e2.
Proof.
   (*That's just explicitely using the default induction principle*)
   induction e1 using exampleType_ind.
Abort. 

Definition holdsForAll (e: exampleType) := True. 



(* That's the default induction principle for exampleType if we defined it ourselves  *)
Definition customExampleType_ind_simpl :=  
   fun (P1 : exampleType -> Prop) 
   (fStep : forall (n : nat) (innerE : exampleType), P1 innerE  -> P1 (StepE n innerE) ) 
   (fbase : forall n : nat, P1 (BaseE n))
   =>
   fix proofFun (anyE : exampleType) : P1 anyE :=  
      match anyE with 
      | BaseE n => fbase n
      | StepE n innerE => fStep n innerE (proofFun innerE) 
      end.

Lemma sum_nonsense : forall e1 e2: exampleType, 
   sum_example e1 = sum_example e2.
Proof.
   induction e1 using (customExampleType_ind_simpl).
Abort.

(*We could also make it a theorem or lemma 
   ... this is just about the arguments it takes (a property and proofs for all constructors)
   and the conclusion that is returned i.e. a proof for the whole type
*)

Lemma customExampleType_ind_lemma:
   forall 
   (P : exampleType -> Prop) 
   (fbase : forall n : nat, P (BaseE n))
   (fStep : forall (n : nat) (innerE : exampleType), P innerE  -> P (StepE n innerE)), 
   forall (e: exampleType), P e.
Proof. 
   (*Instead of an implementation, as in the Definition above, we now give a Proof.
   In a later lecture we'll discuss why we can do that (and why it's cool)*)
   intros P fBase fStep e.
   (*
      Notice that we do not need to proof that any specific P hold here, we just proof that our
      induction principle suffices to give us a proof for all elements of exampleType
   *)
   induction e.
   - apply fBase.
   - apply fStep. apply IHe.
Qed. 

Lemma sum_nonsense : forall e1 e2: exampleType, 
   sum_example e1 = sum_example e2.
Proof.
   induction e1 using (customExampleType_ind_lemma).
Abort.


(*Ok .. but why? 
  Let's use it to actually write some custom induction principle.
  Let's say you want to prove a property that works on pairs instead of single instances of exampleType
*)


Lemma exampleType_pair_ind :
  forall (P : exampleType -> exampleType -> Prop),
    (forall n m, P (BaseE n) (BaseE m)) ->
    (forall n m e, P (BaseE n) (StepE m e)) ->
    (forall n m e, P (StepE n e) (BaseE m)) ->
    (forall n m e1 e2, P e1 e2 -> P (StepE n e1) (StepE m e2)) ->
    forall e1 e2, P e1 e2.
Proof.
  intros P H_BaseE_BaseE H_BaseE_StepE H_StepE_BaseE H_StepE_StepE.
  induction e1 as [n1 | n1 e1' IHe1'].
  - destruct e2 as [n2 | n2 e2'].
    + apply H_BaseE_BaseE.
    + apply H_BaseE_StepE.
  - destruct e2 as [n2 | n2 e2'].
    + apply H_StepE_BaseE.
    + apply H_StepE_StepE.
      apply IHe1'.
Qed.

(*
For further practice and reading:

There are two chapters in the Software Foundations book that give a deeper understanding and more examples on induction. 
One is the chapter *Induction* obviously: https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
The other other is *Induction Principles*: https://softwarefoundations.cis.upenn.edu/lf-current/IndPrinciples.html

*)
