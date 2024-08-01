Definition helper1 {T : Type} (a:T): bool := false.

Definition helper2 (n: nat) : Prop :=
    n = 23. 

Definition somethingElse : Prop := True.


Inductive ExampleType : Type := 
  | FirstConstructor (n: nat) (b : bool)
  | SecondConstructor(n: nat) (b : bool)
  .

Definition as_num (e: ExampleType) : nat := 
   match e with 
   | FirstConstructor n _ => n
   | SecondConstructor n _ => n
   end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).