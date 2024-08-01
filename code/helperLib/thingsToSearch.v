Require Import String.

Inductive expr :=
  | Var (x : string)
  | Lam (x : string) (e : expr)
  | App (e1 e2 : expr)
  | LitInt (n: nat)
  | Plus (e1 e2 : expr).