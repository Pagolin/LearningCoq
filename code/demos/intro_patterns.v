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

(*Intropatterns - Syntax and Examples*)

(*simple_intropattern*)

Lemma star_for_dependent : forall (a b c : nat),
    a = b -> b = a.
Proof.
    (*Introduces _dependent premisses_ i.e. everything that 
      appears in the binder (forall ...) and the statement.
      Hence neither c nor a = b, not nat are introduced *) 
    intros *.
Abort.

Lemma doublestar_for_non_dependent {T: Type}: forall (a b c : T),
    a = b -> b = a.
Proof.
    (*Introduces _dependent_ and _non-dependent premisses_ 
      until only the goal is left.*) 
    intros **.
Abort.



Lemma simple_intropattern {T : Type}: forall (a b c : T),
    a = b -> b = c -> a = c.
Proof. 
    (*naming_intro_pattern - ident*)
    intros a b c.
    (*naming_intro_pattern - ? ... let coq generate a name*)
    intros ?.
    (*naming_intro_patter - ?name ... give coq a prefix for the name to introduce. 
    if that prefix is unique, not postfix will be generated *)
    intros ?H.
Abort.


(*there's three syntaxes to introduce/destruct conjunctions*)
Lemma and_intropattern {T : Type} (a b c : T): 
    (a = b /\ b = c) /\ somethingElse  -> a = c.
Proof.
    intros [[Hab Hbc] Hsomething].
    (* alternatives: 
    intros ((Hab & Hbc) & Hsomething).    
    intros ((Hab, Hbc), Hsomething).
    *)
Abort. 

(*equivalence is just a fancy conjunction, you can destruct it into direction 
 (A -> B) /\ (B -> A) or introduce it as it is (B <-> C)*)
Lemma equivalence_intropattern A B C: 
    (A <-> B) /\ (B <-> C) -> A <-> C.
Proof.
    intros [[Hab Hba] Hbccb].
    (* again alternatives: 
    intros ((Hab & Hbc) & Hbccb).    
    intros ((Hab, Hbc), Hbccb).
    *)
Abort.

(*quantified variables and let-ins are also treated as conjunction*)

Lemma quantifiers {T: Type} (A B: Prop):
    A /\ (exists (var : T), helper1 var = true) -> B.
Proof.
    intros [Ha [eVar Hhelper]].
Abort.


(*disjunction has just one syntax namely [ | | | ]
  as only one them has to be true for the dijunction to hold,
  the goal will be split into 
  as many subgoals as there are disjoint branches i.e. *)
Lemma disjunction A B :  
    A \/ B -> ~(~A /\ ~B).
Proof. 
    intros [Ha | Hb].
Abort.

(*Equality patterns. -> ... similar to rewrite it matches the next 
  hypothesis to introduce and rewrites the goal left-to-right with it.
  The hypothesis must be an equality and is just cleared by that step.
  Obviously there's also <-, to rewrite in the other direction.*)
Lemma equality_rewrite_left {T:Type} (a b c: T) : 
    a = b -> b = c -> a = c.
Proof.
    intros ->.
    intros <-.
Abort.

Lemma equality_apply_injection (a b c d : nat): 
    S a = S d -> S a = S b -> S b = S c -> a = b.
Proof.
    (*applies injection (f_equal) 
      on the next (equality) hypothesis*)
    intros [=].
    (*does the same, but names it*)
    intros [=Hbc].
    (*does the same, but instead of introducing b = c
      uses it to rewrite goal + context*)
    intros [=->]. 
Abort.

Lemma equality_discriminate (n1 n2: nat): 
    FirstConstructor n1 true = SecondConstructor n2 true -> n1 = n2. 
Proof.
    (*applies _discriminate_ on the first hypothesis
      because we claim equality of differnt constructors
      and solves the goal by reducing the hypothesis to False
      btw. Can someone do [discriminate] as the next tactic? *)
    intros [=].
Abort.


(*Applying [] as intro pattern on inductive data types*)

(*If the type has more than one constructor "[]" will produce a goal for 
  each constructor and introduce parameters of the constructors as assumptions*)
Lemma destruct_by_brackets : forall (l :list nat), l = l.
Proof.
    intros [].
Abort.

Inductive singleConstructorType := SCT (b: bool) (n: nat) (e: ExampleType). 
(*If the type has one constructor "[]" will introduce parameters 
  of the constructors as assumptions*)
Lemma destruct_by_brackets' : forall (sce : singleConstructorType), sce = sce.
Proof.
    intros [].
Abort.

Lemma same_with_props (A B C D : Prop) : A /\ B -> C \/ D -> A /\ C \/ D.
Proof.
    intros []. (*Produces two hypothesis because there's just one constructor for a conjunction*) 
    intros []. (*Produces two goals, actually two contexts for the same goal
                 because there's two constructors for a disjunction*)
Abort.

Lemma destruct_by_brackets'' : 
    forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros n []. (*Destructs m and produces goals for m=0 and m = S m'*)
    - intros [].  (*used on equalities it performs a <- rewrite ??? *)
Abort. 


Lemma destruct_by_brackets'' : 
    forall n m p: nat, n + m = p -> n = p - m /\ m = p - n.
Proof.
    intros n [] p. (*Destructs m and produces goals for m=0 and m = S m'*)
    - intros [=<-].  (*Question: Are [] and [=<-] or [=->] equivalent?*)
Abort. 


(*Caution ... when used on false equalities "[]" just clears the hypothesis i.e. introduces nothing and
  removes the False assumption. You want to use "[=]" on false equalities*)

Lemma caution_with_brackets : forall (n m:nat), S n = n -> n = m.
Proof. 
    intros *.
    intros [].
Abort.

(*Directly apply a lemma/function to the things you introduce using "%"*)
Definition matching_example (n : nat): ExampleType := FirstConstructor n true.


Lemma add_succesors : forall (a b c: nat), b + c = c + b.
Proof.
    intros a%matching_example b c.
Abort. 


(*Combining intro patterns:*)

(*helper definition*)
Theorem length_zero_iff_nil {A: Type} (l: list A) : 
   length l = 0 <-> l = nil.
Proof.
    destruct l; simpl.
    - split; reflexivity.
    - split; intros [=].
Qed.  


(*the usual intros/intros** *)
Lemma stolen_from_docu {T: Type} (xs ys : list T):
    S (length ys) = 1 -> xs ++ ys = xs.
Proof.
    intros. 
Abort.
    
(*introducing plus applying injection/discriminate
 "unwraping constructor equality"*)
Lemma stolen_from_docu' {T: Type} (xs ys : list T):
    S (length ys) = 1 -> xs ++ ys = xs.
Proof.
    intros [=]. 
Abort.

(*introducing, "unwraping constructor equality"
  and directly applying the result to a given function/theorem
  For whatever reason the order here is 
  1. strip equality to lenght ys = 0 by [=]
  2. apply to theorem length_zero_iff_nil by %
  3. rewrite with ys = nil by -> *)

Lemma stolen_from_docu'' {T: Type} (xs ys : list T):
    S (length ys) = 1 -> xs ++ ys = xs.
Proof.
    intros [=->%length_zero_iff_nil]. 
Abort.
    
(*-----------------------------------------------------*)
(*Notes on usage by/in tactics: *)

(* According to the docu *)

(*(e)intros uses [intropattern*] ... we've seen that*)

(* Most tactics use [simple_intro_pattern] -> means anything but */** *)

(* (e)destruct, (e)induction, (e)case and inversion use 
   [or_and_intropattern] ... means lists or tuples of intropatterns for conjunction and disjuntion
   
    ... or constructors of inductive types, e.g. [destruct someBool] omiited in the docu*)

(* many tactics have a buildtin [eqn:] which uses [naming_intropattern] i.e. ? | ident | ?prefix | _ *)