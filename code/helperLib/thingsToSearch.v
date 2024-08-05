(*The examples here are taken from the semantics course material on the separation 
  logic framework Iris, available at
  https://plv.mpi-sws.org/semantics-course/
*)

Require Import String.
Inductive expr :=
  | Var (x : string)
  | Lam (x : string) (e : expr)
  | App (e1 e2 : expr)
  | LitInt (n: nat)
  | Plus (e1 e2 : expr).

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Definition is_val (e: expr): Prop := 
  match e with
  | LitInt n => True
  | Lam x e => True
  | _ => False
  end.

Inductive val :=
  | LitIntV (n: nat)
  | LamV (x : string) (e : expr).


(* Turn values into expressions*)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  end.

(* try to turn expressions into values *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v; simpl; reflexivity.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e; simpl; try congruence.
  all: injection 1 as <-; simpl; reflexivity.
Qed.



(** *** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | LitInt n => LitInt n
  | Var y => if (eqb x y) then es else Var y
  | Lam y e =>
      Lam y (if (eqb x y) then e else subst x es e)
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Plus e1 e2 => Plus (subst x es e1) (subst x es e2)
  end.


(** *** Small-Step Semantics *)
(* We use right-to-left evaluation order,
   which means in a binary term (e.g., e1 + e2),
   the left side can only be reduced once the right
   side is fully evaluated (i.e., is a value). *)
Inductive step : expr -> expr -> Prop :=
  | StepBeta x e e'  :
      is_val e' ->
      step (App (Lam x e) e') (subst x e' e)
  | StepAppL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
  | StepAppR e1 e2 e2' :
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
  | StepPlusRed (n1 n2 n3: nat) :
    (n1 + n2)%nat = n3 ->
    step (Plus (LitInt n1) (LitInt n2)) (LitInt n3)
  | StepPlusL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (Plus e1 e2) (Plus e1' e2)
  | StepPlusR e1 e2 e2' :
    step e2 e2' ->
    step (Plus e1 e2) (Plus e1 e2').

(* We make the tactic eauto aware of the constructors of [step].
   Then it can automatically solve goals where we want to prove a step. *)
#[global] Hint Constructors step : core.


(*Simple example of a user defined tactic.*)
Ltac user_def_invert H :=
  inversion H; subst; clear H.


(*Examples for Scopes*)

Inductive penguins : Set := 
  | Penguinegg 
  | Penguin
  | Huddle (n: nat).

Definition huddle (p1 p2: penguins) : penguins := 
  match p1 with
  | Huddle n => match p2 with 
                 | Huddle m => Huddle (n + m)
                 | _        => Huddle (S n)
                end
  | _        => Huddle (S (S 0))
  end.

Declare Scope penguins_scope.
Delimit Scope penguins_scope with Peng.
Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Notation "p1 + p2" := (huddle p1 p2)
                      (at level 50, left associativity)
                       : penguins_scope.

Notation "e1 + e2" := (Plus e1%E e2%E) : expr_scope.