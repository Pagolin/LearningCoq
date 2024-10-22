(* ------------- First things first ... What is *Induction*? ----------------------------------*)


(* Induction is the principle of concluding a general thing (theory/hypothesis/fact) from examples.
You've seen a lot of large, white, swimming birds with long necks and all of them have been called swan, so you
conclude the general principle of calling large, white, swimming birds with long necks swans.  

The oposite principle is deduction. Concluding facts about concrete instances from a general 
fact/theory/definition. To stick with the swan example, if someone tod you the definition of swan
you could deduce for one particular bird, if it's a swan or not. 


Inductive Datatypes are hence inductive because you define them by giving all the 
instances that could make up a member of that type and "conclude" the type. 
from the definition coq concludes (because it requries this) that
   - those constructors are the only ways to build the type
   - you can build any of the recursive instances based on non-recursive instances of the
     type 
*)


(*Let's have an inductive structure*)

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
    1. a predicate P that maps elements of exampleType to a Property 
       P: exampleType -> Prop  ... meaning it may or may not hold
    2. a function f that gives you P (BaseE n) for all n
       meaning you proof P holds for the Base element
    3. a function f0 that gives you P (StepE ... ) if you give it a P innerE
  
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

4. Since the basic elements fullfil the property, and every building step you can make preserves the property
   the property holds for everything you can build. 

So let's look at an example
*)



Fixpoint sum_example (e: exampleType) : nat := 
 match e with 
 | BaseE n => n
 | StepE n innerE => n + sum_example innerE
 end.

(*ToDo: Find a less pointless example*)
(*Let's do an inducitve proof using the induction principle directly*)
Lemma sum_bigger_0 : forall e:exampleType, sum_example e >= 0.
Proof.
    apply exampleType_ind.
    (*applying the induction hypothesis directly gives you backward reasoning i.e. 
      1. it matches the conclusion/return term of the induction principle with
      the goal .. that's ohw it figures out P
      2. it replaces the original goal with the 'input function' of the induction
         principle i.e. the function to proof P for the base element and
         the function to proof P for the step 
      *)
   - intro n.
     apply le_0_n.
   - intros n innerE IH.
     (* Now we introduced the induction hypothesis by hand and are essentially 
         at the same point as we'd been using the induction tactic*)
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

(*Knowing that the induction tactic will introduce 
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


(* ToDo: 
   1. general syntax of [induction]
   2. example for using it with different terms when there are multiple option in a proof
   3. example for using it with different induction principles and custom properties 
   Question: Do we really want number 3 ? I think it's not necessary in the beginning ie. to
   generally understand how it works and might rather convey a feeling of information overload
   without direct practical use.  

*)
(*------------------------ -----------------------------------*)




(*Comments from Sebastian -> ToDo's for me  

1. ToDo: Factor into the general explanation of induction principles: 

  "In both of the approaches above and the things
  that we tried together we had the wrong strategy.

  Let's recap:
  What does induction mean?
  - I have an inductive data type, say this simple one:
    [ Inductive A : Set :=
      | a : A
      | b : A -> A
    ]
    (Of course, this is isomorphic to [nat].)

  - I have a lemma saying: [P: A -> Prop].
  - Now the induction hypothesis that I get is telling me something
    about the recursive call of [b]!
    That is,
     [Lemma p : forall a:A, P a.]
    When I do [induction a] then I get two cases:
    1. case -> base case
    2. case (a = b a0) -> inductive case
       The important thing here is the induction hypothesis which is [IH: P a0].
       Take a deep breath and read this again:
       The induction hypethesis talks about the recursive case only!
       The strategy is then always the same:
       Apply the IH *to the children*(!) and then use this fact to solve the goal, i.e.,
       generalize to the parent.

   --> Our fault was that we were trying to use the IH to *directly* solve the
       goal! That is not possible.

    Let's give it another try then:"

2. ToDo: There's an example of defining P ourselfs and applying the _ind hypothesis
         with this directly

   "Definition P (x:string) (e:expr) : Prop :=
    (∃ e0 : expr, e = (x e0)%E) ∨ (∃ v : val, e = (x v)%E).

   Lemma no_var_app_aux : forall (x:string) e e',
         rtc step ((Var x) e) e' -> P x e'.
   Proof.
      move => x e e' H.
      move: e' H.
      apply (rtc_ind_r (P x) (x e)); rewrite /P.
   "

   Reminder: rtc_once/_r/_inv/_ind_l/_ind_r are not auto-generated induction priciples but derived lemmata from stdpp
   https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.relations.html

3. ToDo: To explain this behaviour I need the section from the documentation, that explains how induction works 
         on nested inductive/recursive types
   "(* Check this out:
         The induction hypothesis is defined over
         the individual steps, not over the rtc-child itself.
         That is different as compare to the induction
         principle of say [nat].
         That might also be the reason why there are several
         induction principles for rtc.
       *)
   "
   => see reminder above ... the different induction principles are not auto-derived and not explained/enforced by structure,
      but are convenient helpers from the library 

*)

(*
From SFV1.

There are two chapters in the Software Foundations book that give a deeper understanding and more examples on induction. 
One is the chapter *Induction* obviously: https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
The other other is *Induction Principles*: https://softwarefoundations.cis.upenn.edu/lf-current/IndPrinciples.html

*)