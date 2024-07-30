From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.

(*ToDo. Replace examples*)
From semantics.ts.stlc Require Import lang notation.
From semantics.ts.stlc Require untyped types.


(*In general:

What is it?                                 -> About
Where is it defined?                        -> Locate | Print Scope 
How is it defined?                          -> Print 
Where is it used and what can I do with it? -> Search

*)


(*About **)
(* displays 
    - kind (module, constant, assumption, inductive, constructor, abbreviation, …)
    - long name
    - type
    - implicit arguments and argument scopes.
    - no definitions or proofs**)
About expr.

(*Locate *)
(*tells you where to find the definition for a qualified identifier*)
Locate expr.

(*tells you where to find the defitition of notations .. there might be many different*)
Locate "+".

(*You can search for files*)
Locate File "types.v".

(*You can restrict the search to terms ... in this example I'm using a constructor (as the search will tell
you) so the restriction is not particularly useful*)
Locate Term LitInt.

(*Will tell you there is non because it's int he file tree but not loaded*)
Locate Module cbn_logrel.

(*Will tell you the logical path, because it's a loaded module*)
Locate Module gmap.



(*Print the definition of defined objects*)
Print expr.

(*ToDo: Doesn't make sense outside of a proof.*)
Print All.

(*The Set expr has no dependencies so it says "Closed under the global context"*)
Print All Dependencies expr.

(*The lemma says 
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Checking it's dependencies will hint you to 
  Transparent constants (ie. thing that are more or less explicitly used )
  to_val, of_val, f_equal, False_ind ..
  and Opaque constants, which in this case is just the lemma itself*)
Print All Dependencies of_to_val.
(*Restrict the output of the above*)
Print Opaque Dependencies of_to_val.
Print Transparent Dependencies of_to_val.


(*ToDo: Doesn't make sense outside of a proof*)
Print Assumptions typed_weakening.


(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2
*)


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.


Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)


(* Lists all the loaded databases 
   and tactics therein mentioning or relevant to the 
   big_step relation
  Hints can be declared ie. written into the databases 

  #[export] Hint Constructors big_step : core.

  This writes a constructor hint into the core db.
*)
Print Hint big_step.

(*basically spells out, what the type definition tells regarding
 implicit arguments*)
Print Implicit f_equal.

(*Prints the tactics definition if it is user defined.
  If you ask for a library tactics like <reflexivity> this will probably
  just be a hint to underlying definitions *)
Print Ltac simplify_val.

(*Print all notations defined in the scope
  I declared foe expressions i.e. 
  Declare Scope expr_scope.
**)
Print Scope expr_scope.
(*Try out with overloaded set names**)

(*Gives you a rather long list of all notations
  you have currently available and the scopes they belong to*)
Print Scopes.
(*If you know the notation and want to locate it use: *)
Locate "(.⊔ y )". 


(*Search **)

(* Search _qualid_ gives all objects (theorems, lemmas etc)  that contain _qualid_.
  Containing means use it/depend on it (not "substring-name-contain" although that often overlaps ) *)

Search rev.

(** When you Locate a Notation you search for the definition i.e. the rhs ... so you locate the string.
    When you Search the use of a Notation you use it as the parser sees it i.e. not as a string*)

Search (_ + _ = _ + _). (*That's the _term-pattern_ search from the docu**)

(* We can filter the textwall of results by restricting it to modules*)

Search (_ + _ = _ + _) inside Nat.

(* We can be structurally more specific by using variable names "?n" instead of wildcards*)

Search (?x + ?y = ?y + ?x). (*That's the _term-pattern_ search with non-linear results from the docu**)

(*We can search for strings, iff they are either a valid identifier or a defined Notation 
  string. Again what we'll get from searching is not the defintion but the usages of the term/object we search *)

(* Search "_ + _".          works because it's a defined notation*)
(* Search "_ + _ = _ + _".  doesn't work because it combines notations*)

Search le_n.
Search "le_n".


(*Again we can filter by scopes*)
Search "_ + _"%E. (*anything that uses addition on expressions*)

(*Searching for the combined usage of dfifferent things*)

Search expr subst'. (*Searching for uses of expr and subst*)
Search expr "subst".  (*Searching for uses of expr that have "subst" in their name*)
Search expr subst' "base". (* when you know the lemma was something with "base" in it*)

Search expr subst' outside lang. (*Again we can search inside and outside of specific modules*) 

Search expr subst' - is_val. (*Exclude the term "is_val" from the search results*)
Search expr subst' - "big". (*Exclude anything named ".*big.*" (containing the substring big) from the search results*)
