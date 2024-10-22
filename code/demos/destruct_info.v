Require Import Arith.
Require Import List.
Import List.

(* Inductive mynat: Type:=
| O
| S (n : mynat). *)

Inductive colors: Type:=
| red (n:colors)
| green (n:colors)
| blue (n:colors)

.

Print colors.
Print colors_rect.

(* The destruct tactic separately considers the cases where n = O and where n = S n'. 
  It generates two subgoals, which are proven separately *)

Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n as [| a] eqn:E.
Abort.

(*The annotation "as [| n']" (OPTIONAL) is called an intro pattern. 
  It tells Coq what variable names to introduce in each subgoal. 
  In general, what goes between the square brackets is a list of lists of names, separated by |.
  In this case, the first component is empty, since the O constructor doesn't take any arguments. 
  The second component gives a single name, n', since S is a unary constructor. 
  *)

(* With intro pattern*)


Definition everything_is_true (c:colors) := True.

Theorem something_about_colours : forall c:colors, everything_is_true (c)=True.
Proof.
intros c.
destruct c as [r | g | b].
Abort.

(* Without intro pattern*)

Theorem something_about_colours : forall c:colors, everything_is_true (c)=True.
Proof.
intros c.
destruct c.
Abort.

(*   The eqn:E annotation (OPTIONAL) tells destruct to give the name E to this equation.  
The - signs on the second and third lines are called bullets, 
and they mark the parts of the proof that correspond to the two generated subgoals.
*)


Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n.
  - simpl. reflexivity.
  - unfold Init.Nat.add. simpl. reflexivity.
Abort.

(* Marking cases with bullets is optional
If bullets are marked Coq ensures that a subgoal is complete before moving to the next one *)

Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
  Abort.

(* Besides - and +, we can use × (asterisk) or any repetition of a bullet symbol (e.g. -- ) as a bullet.
It is sometimes useful to invoke destruct inside a subgoal, generating yet more proof obligations. 
In that case, different types of markers are required for different types of sub-goals*) 

Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - destruct n.
    + reflexivity.
Abort.

(* Subgoals can also be enclosed in curly braces *)
Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n.
  { reflexivity. }
  { destruct n.
    { reflexivity. }}
Abort.

(*Curly braces can be mixed with bullets as well*)
Theorem add_1_neq_0 : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n.
  - reflexivity. 
  - destruct n.
    { reflexivity. }
Abort.

Theorem add_1_neq_0_ind : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - reflexivity.
Qed.

(* Can also be used with data types like list *)

Definition l:= 3::2::1::nil.

(*Function to obtain tail/ remove head from list*)
Definition behead (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* Destruct on a list data type*)

Theorem tl_length_pred :
  pred (length l) = length (behead l).
Proof.
  intros. destruct l as [| n l'].
  - reflexivity.
  - reflexivity. Qed.

(* Destruct can also be used to reason by cases on result of some expression*)

Definition falsefun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem falsefun_false : forall (n : nat),
  falsefun n = false.
Proof.
  intros n. unfold falsefun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.
