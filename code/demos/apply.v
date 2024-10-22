From lib Require Import basics.
(*Tactics for applying theorems  ...  [exact] and [apply] *)

(*------------------------------- [exact]--------------------------------------*)

(*Syntax 

  exact one_term

  where 
  one_term ... a qualified identifier for a term (lemma, theorem, function)
*)

(*General Principle: 

  Iff the types of _one_term_ and the goal can be unified exact solves the goal, otherwise it fails.
  Unification as in "bringing types into the same shape" follows conversion rules as alpha-conversion, beta-reduction a.s.o. 
  described in the documentation https://coq.inria.fr/doc/V8.18.0/refman/language/core/conversion.html#conversion-rules 
*)

(*ToDO: Example*)


(*------------------------------- [apply]--------------------------------------*)
(*Syntax 

    apply one_term_with_bindings+, in_hyp_as?


    What to apply :

    one_term_with_bindings+, is a comma separated list of one_term_with_bindings
    
    one_term_with_bindings := one_term __with__ bindings

    one_term ... a qualified identifier for a term (lemma, theorem, function)

    bindings := 
        one_term+ ... an ordered sequence of terms for the arguments/variables of the term (lemma, theorem ... ) you want to apply
       |(ident | nat := term) ... explicitly name or enumerate the arguments of the term (lemma, theorem ...) you want to apply and assign a term to them          
    

    Where to apply it:

    in_hyp_as ... comma separated list specifiying names of hypotheses and names to give 
                  to give to the outcome of the application 
    
    in_hyp_as := __in__ ident as_ipat?+,
    as_ipat   := as simple_intropattern

    e.g. apply lemmaA in somehypothesis as firstApp, in otherhypothesis as secondApp.
*)

(*Generall principle:
 
 Your environment is 

    H: A
    -------
    B

  ... and you have a term [usefullTerm: A -> B].

  You can forward reason (as in moving towards the goal),
  by applying usefullTerm to the hypothesis H.

  apply usefullTerm in H as newH.

     newH: B
     ---------
     B
  
  Or backward reason (as in reasoning backwards from the goal),
  by applying usefullTerm to the goal.

  apply usefullTerm.

  
    H: A
    -------
    A
  
  In both cases, unification is used to try and match the types of the applied term and the goal or hypothesis. 
  Iff unification succeeds on "one end" i.e.the premisses or the conclusion of the goal/hypothesis, the remainder
  of the matching i.e. non-matched premisses or conclusions will be left as new goal or new assumption. 
*)



(*Examples - forward reasoning
  In forward reasoning, <apply> tries to unify the premises of the term you apply, and the term you apply it to 
  to. In the minimal example above you hav a hypothesis A and a term A->B
  so you can conclude (A /\ A -> B) -> B and get a new hypothesis B
*)




(*Examples - backward reasoning*)

(*trivial case ... the applied term matches the goal exactly and solves it.*)

Lemma exact_match : forall (A B C: Prop), (A -> B -> C ) -> A -> B -> C.
Proof. 
  intros  A B C H.
  apply H.
Qed.

(*The suffixes of the goal and the applied term match
  i.e. the conclusion and some premisses match but the applied term 
  has more premisses than the goal  *)
Lemma partial_goal_match : forall (A B C: Prop), A -> (A -> B -> C ) -> B -> C.
Proof. 
  intros  A B C HA HBC.
  apply HBC.
  apply HA.
Qed.

Lemma partial_goal_match' : forall (A B C: Prop), A -> (A -> B -> C ) -> B -> C.
Proof. 
  intros  A B C HA HBC.
  apply HBC, HA. (*using the comma separated notation is equivalent to multiple [apply term] usages*)
Qed.


Inductive singleConst := SConstructor (n1 : nat) (n2 : bool) (p:Prop).

Lemma conclude_singleConst (n1 n2 : nat) (b: bool) (p: Prop): singleConst .
Proof.
  apply SConstructor.   


(*   Without in_hyp_as (the goal case)


        If the conclusion of the type of one_term does not match the goal 
        and the conclusion is an inductive type with a single constructor, 
        then each premise in the constructor is recursively matched to the goal 
        in right-to-left order and the first match is used. 
        In this case, the tactic will not match premises that would result in applying a lemma of the form forall A, … -> A. See example here.

        The goal case uses first-order unification with dependent types unless the conclusion of the type of term is of the form P t1 … tn with P to be instantiated. 
        In the latter case, the behavior depends on the form of the target. If the target is of the form Q u1 … un and the ti and ui unify, then P is instantiated into Q. Otherwise, apply tries to define P by abstracting over t1 … tn in the target. You can use pattern to transform the target so that it gets the form (fun x1 … xn => Q) u1 … un. See the example here.
*)

(*With in_hyp_as*)

(** Here's another example of using a theorem like a function.

    The following theorem says: if a list [l] contains some element [x],
    then [l] must be nonempty. *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.


Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis (causing the values of the
    other parameters to be inferred). *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.
