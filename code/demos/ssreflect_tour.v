
(** * Introduction to SSReflect

  Central ideas:
  - Reduce the number of tactics needed.
  - Work in the goal only and leave the context untouched.

  Resources:
  - the reference manual: https://coq.inria.fr/doc/v8.19/refman/proof-engine/ssreflect-proof-language.html
  - the tutorial (pdf) by Gonthier and Le: https://inria.hal.science/inria-00407778/document

 *)

(** ** Loading
  Drop the following lines into your Coq file
  to start using SSReflect.
  Please beware: after interpreting the next lines
  standard tactics such as [rewrite] and [apply]
  will be shadowed by SSReflect's versions.
 *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ABC.
  Variable A B C: Prop.

  (** ** The goal stack.

    This is basically just terminology.
    The goal stack is the goal.
    When the goal is not a function then the goal stack is of size 1.
   *)

  Lemma goal_stack_1 : A /\ B.
  Proof. Abort.

  (*
  In the following goal, the goal stack is of size 2.
  The top of the goal stack is the leftmost assumption.
  In this example, it is [A].
   *)

  Lemma goal_stack_2 : A -> A \/ B.
  Proof. Abort.

  (*
  Just as an exercise:
  This goal stack is of size 5.
   *)
  Lemma goal_stack_4 : A /\ B -> A -> B -> A \/ B.
  Proof. Abort.

  (** ** Push and pop
      To manipulate the goal stack there exist two operations:
      - popping, i.e., removing, the top of the goal stack and
      - pushing a new type onto (the top of) the goal stack.
   *)
  Lemma pop : A -> A /\ B.
  Proof.
    move => HA.
    (* Here [move] is a no-op tactic.
       The [=>] actually moves the top of the goal stack into the context.
       That means, you can write [X => ...] where is any tactic.
     *)
    Restart.
    (* Of course, [move =>] is then just your normal [intro]. *)
    intro HA.
  Abort.

  Lemma push : A /\ B.
  Proof.
    move: A.
    (* Once more, [move] is a no-op and the pushing is actually
       performed by [:].
       As such, also [:] can be combined with several other tactics.
     *)
    Restart.
    (* Yes, [move:] is just [revert]. *)
    revert A.
  Abort.

  (*
    You may pop and push multiple variables in one go.
   *)

  Lemma pop_push_2: A -> B -> A /\ B.
  Proof.
    move => HA HB.
    move: HA HB.
    (* and the same in normal Coq tactic slang *)
    intros HA HB.
    revert HA HB.
  Abort.

  (*
    Intro patterns work as usual.
    Destructuring.
   *)
  Lemma intro_patterns_up_1: A /\ B -> B /\ A.
  Proof.
    move => [HA HB].
    Restart.
    intros [HA HB].
  Abort.

  (*
    Destructuring with multiple cases.
   *)
  Lemma intro_patterns_up_2: A \/ B -> B /\ A.
  Proof.
    move => [HA | HB].
    Restart.
    intros [HA | HB].
  Abort.

  (** ** Case analysis.
      Looking at the example before, we are already in
      the realm of reasoning by cases.

      The above example is better expressed as follows.
   *)
  Lemma case_1: A \/ B -> B /\ A.
  Proof.
    case.
    (* That way I can see in the goal what is going on
       while the context remains untouched.
     *)
    Restart.
    intro H; destruct H.
    (* [destruct] works as the [move] with intro pattern
       from above.
     *)
  Abort.

  (*
    Destructuring can also be performed on the way down.
   *)
  Lemma intro_patterns_down (H: A /\ B): B /\ A.
  Proof.
    case: H.
  Abort.

  (*
    It is sometimes necessary to store the equation.
    In fact, [case] generates equalities.
   *)
  Lemma case_E (H: A /\ B): B /\ A.
  Proof.
    case E: H.
    (* If you want to store the equation then please give names! *)
    Restart.
    case E: H => [HA HB].
  Abort.

  (** ** Application
      Application works solely on the top of the goal stack.
   *)

  Lemma apply_1 (H: B -> A): A.
  Proof.
    apply/H.
    Restart.
    apply H.
  Abort.

  (*
    Note, that the above reasoning of [apply] is backwards.
    If the goal stack is larger than 1 then the reasoning is forward.
    Hence, we [move] instead of [apply].
   *)

  Lemma apply_2 (H: B -> A): B -> C.
  Proof.
    Fail apply/H.
    move/H.
  Abort.


  (*
    Apply-away.
   *)

  Lemma apply_3 (H1: B -> A) (H2: A -> B): A.
  Proof.
    apply/H1/H2.
    Fail move/H1/H2.
  Abort.

  (*
    Move-away.
   *)

  Lemma apply_4 (H1: B -> A) (H2: A -> B): B -> C.
  Proof.
    move/H1/H2.
    Fail apply/H1/H2.
  Abort.

  Lemma apply_5 (H1: B -> A): B -> A.
  Proof.
    apply: H1.
    Restart.
    exact: H1.
    Restart.
    move: H1; exact: id.
  Abort.

  (* Constructing an application and applying the result. *)
  Lemma apply_6 (H1: B -> A) (b:B) : A.
  Proof.
    apply: H1.
    Restart.
    apply: (H1 b).
  Abort.

  (* Applying in the goal stack. *)
  Lemma apply_7 (H1: B -> A) (b:B) : A.
  Proof.
    apply/H1: b.
  Abort.

  (** ** Rewriting and all that
      Rewriting is the true super-power of SSReflect.
      The algorithm for rewriting is strictly more powerful than
      the usual [fold]/[unfold]/[rewrite].
      Plus, guided-rewriting is super convenient.
   *)
  Lemma rewrite_1 (H: B = A) : B -> C.
  Proof.
    (* left to right *)
    rewrite H.
    (* right to left *)
    rewrite -H.
  Abort.

End ABC.

  (*
    Unfolding is of course rewriting!
   *)
  Lemma rewrite_2 : forall n m, n * m = 0.
  Proof.
    (* unfold *)
    rewrite /Nat.mul.
    (* fold *)
    rewrite -/Nat.mul.

    (* Notations work too. *)
    rewrite /(_ * _). (* no-op, because [rewrite] never errors out. *)
    move => n m; rewrite /(_ * _).
    rewrite -/(_ * _).
  Abort.

  Lemma rewrite_3 : forall n m, n * m = m * n.
  Proof.
    (* On default, rewrites apply to the whole goal stack. *)
    rewrite /Nat.mul.
    rewrite -/Nat.mul.

    (* Rewrite restricted to the left-hand side only. *)
    Fail rewrite [X in forall _ _, X = _]/Nat.mul.
    move => n m.
    rewrite [X in X = _]/Nat.mul.
    (* Shorter *)
    Fail rewrite -[LHS]/Nat.mul.
    rewrite -[LHS]/(Nat.mul _ _).

    (* Of course, there is [RHS] too. *)
    rewrite [RHS]/Nat.mul.
  Abort.


  (** ** Induction
      Again, the key is to reduce the number of tactics.
      In standard Coq, you may use [induction] or [dependent induction].
      A dependent induction allows reasoning about dependent types
      such as length-indexed vectors.
   *)
  Lemma elim_1 : forall n m, n * m = m * n.
  Proof.
    (* Works the same as case. *)
    elim.
    Restart.
    (* Again, [elim: Hn] is just the same as [move: Hn; elim] *)
    move => Hn; case: Hn.
    intro n. induction n.
  Abort.

  (*
    Note that the [induction] tactic always works in the context.
    And it changes your context too.
   *)
  Lemma elim_2 n m (H:n = 0) : n * m = m * n.
  Proof.
    induction n. (* Check out how [H] changed.
                    In PG, I cannot see the effect because I cannot see
                    the context of the second goal. *)
    Restart.
    (* Of course, SSReflect would not allow to do a blank induction on [n]. *)
    Fail elim: n.
    (* We need to move all the dependent hypothesis down into the goal stack.
       This also resolves dependent type induction where [dependent induction]
       would have been necessary.
     *)
    elim: n H.
  Abort.

  (*
    Pick you induction principle.
   *)

  Theorem strong_induction : forall P : nat -> Prop,
      (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
      forall n : nat, P n.
  Proof. Admitted.

  Lemma elim_3 : forall n m, n * m = m * n.
  Proof.
    elim/nat_ind.
    Restart.
    elim/strong_induction.
  Abort.

  (** ** Forward reasoning *)

  Lemma have_1 : forall n m, n * m = m * n.
  Proof.
    have fact: forall n, n = 0. { admit. }
    (* [fact] is readily available in my context. *)
  Abort.


  (** ** Automation, simplification, termination *)

  (* [//] tries to solve simple goals but will never error out of it cannot. *)
  Lemma auto_1 : forall n, n + 0 = n.
  Proof.
    move => //.
  Abort.

  Lemma auto_2 : forall n m, n * m = n + m.
  Proof.
    move => //.
  Abort.

  (* [/=] simplifies but does not solve. *)
  Lemma auto_3 : forall n, 0 + n = n.
  Proof.
    move => /=.
  Abort.

  (* You can combine [//] and [/=] as [//=]. *)

  (** ** Reflection *)

  Lemma reflect_1 (n m:nat): n = m.
  Proof.
    Fail apply/eqP. (* Needs mathcomp or stdpp. *)
    
