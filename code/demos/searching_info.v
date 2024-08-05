Require Import String.
Require Import Arith.
From lib Require Import thingsToSearch. 
(* 
   Here we will have a look a vernacular commands, that help us navigate the code, and find informations 
   about where and how things in our codebase are defined and used. 
   The full documentation can be found at: 

*)

(*In general:

Your Question:                              |   Command
-----------------------------------------------------------------------
What is it?                                 | About
Where is it defined?                        | Locate | Print Scope 
How is it defined?                          | Print 
Where is it used and what can I do with it? | Search

*)

(*About **)
(* displays 
    - kind (module, constant, assumption, inductive, constructor, abbreviation, …)
    - long name
    - type
    - implicit arguments and argument scopes.
    - no definitions or proofs**)

About string.
About expr.
About intros.
About thingsToSearch.


(*Locate *)
(*tells you where to find the definition for a qualified identifier*)
Locate expr.

(*tells you where to find the defitition of notations .. there might be many different*)
Locate "+".

(*You can search for files*)
Locate File "intro_patterns.v".

(*You can restrict the search to terms ... in this example I'm using a constructor (as the search will tell
you) so the restriction is not particularly useful*)
Locate Term LitInt.

(*Will tell you there is non because it's int he file tree but not loaded*)
Locate Module basics.
Require Import lib.basics.

(*Will tell you the logical path, because it's a loaded module now*)
Locate Module basics.


(**************Print*************)

(*Prints loaded i.e. available library files. It may also print which of them is imported 
  but that doesn't always seem to work*)
Print Libraries.

(*Print the definition of defined objects*)
Print expr.

(* Print All.
   ToDo: Clarify
   Documentation says : 
    "This command displays information about 
    the current state of the environment,
    including sections and modules."
   Observable effect: prints only local dependencies (see someProp vs is_val)
*)
Section Demosection.

  Definition someProp (n: nat) : Prop := n = 23.
  Section InnerDemoSection.

    Lemma example : forall (A B C :Prop) (n : nat) (e: expr), 
        A /\ B -> someProp n -> is_val e -> A \/ B.
    Proof. 
      intros.
      Print All.
    Abort.

  End InnerDemoSection.
End Demosection.




(* Print Assumptions: 
  "This commands display all the assumptions (axioms, parameters and variables)
    a theorem or definition depends on. 
    Especially, it informs on the assumptions with respect 
    to which the validity of a theorem relies."

    The example is taken from Software Foundations Vol. 1 
    (https://softwarefoundations.cis.upenn.edu/lf-current/index.html)
*)


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.


Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. 
  intros x.
  apply Nat.add_comm.
Qed.

Print Assumptions function_equality_ex2.

(*Variants of [Print Assumptions]: *)
(*The Set expr has no dependencies so it says "Closed under the global context"*)
Print All Dependencies expr.
Print All Dependencies is_val.

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


(* Lists all the loaded databases 
   and tactics therein mentioning or relevant to the earch term, in
   this case the step realtion among two expressions.
   Such hints can be declared ie. written into the databases 

    #[export] Hint Constructors big_step : core.

   This writes a constructor hint into the core db, so
   tactics like eauto can automatically find and use it to
   solve a goal.
*)

Print Hint step.


(*basically spells out, what the type definition tells regarding
 implicit arguments*)
Print Implicit f_equal.

(*Prints the tactics definition if it is user defined.
  If you ask for a library tactics like <reflexivity> this will probably
  just be a hint to underlying definitions *)
Print Ltac user_def_invert.


(*Gives you a rather long list of all notations
  you have currently available and the scopes they belong to*)
Print Scopes.

(*Print all notations defined in a particular scope. *)
Print Scope expr_scope.

(*If you know the notation and want to locate it use: *)
Locate "+". 


(*Search **)

(* Search _qualid_ gives all objects (theorems, lemmas etc)  that contain _qualid_.
  Containing means use it/depend on it (not "substring-name-contain" although that often overlaps ) *)

Search expr.

(** When you Locate a Notation you search for the definition i.e. the rhs ... so you locate the string.
    When you Search the use of a Notation you use it as the parser sees it i.e. not as a string*)

Search (_ + _ = _ + _). (*That's the _term-pattern_ search from the docu**)

(* We can filter the textwall of results by restricting it to modules*)

Search (_ + _ = _ + _) inside Nat.

(* We can be structurally more specific by using variable names "?n" instead of wildcards*)

Search (?x + ?y = ?y + ?x). (*That's the _term-pattern_ search with non-linear results from the docu**)

(*We can search for strings, iff they are either a valid identifier or a defined Notation 
  string. Again what we'll get from searching is not the defintion but the usages of the term/object we search *)

Search "_ + _".          (*works because it's a defined notation*)
(* Search "_ + _ = _ + _".  doesn't work because it combines notations*)

(* Searching for something particular, 
   i.e. uniquely identifyable in the current environment
   or search for it as  a substring *)
Search Nat.add.
Search "add".


(*Again we can filter by scopes*)
Search "_ + _"%E. (*anything that uses addition on expressions*)
Search "_ + _"%nat. (*anything that uses addition on natural numbers*)

 

(*Searching for the combined usage of different things*)

(*Searching for uses of expr and subst*)
Search expr subst. 

(*Searching for uses of expr that have "subst" in their name*)
Search expr "subst".  

(*When you know you search a lemma about strings that has
 was something with "eq" in it*)
Search string "eq". 

(*We can search inside and outside of specific modules*) 
Search expr subst outside thingsToSearch. (*Nothing to see here*) 
Search expr subst inside thingsToSearch.


Require Import ZArith.

Search Z.add Z.mul "distr".
(*Excluding the object [Prop] from the search results*)
Search Z.add Z.mul "distr" -Prop.
(*Same search, different notation. *)
Search "+"%Z "*"%Z "distr" -Prop. 
(*Search definitions that contain the substring "add"
  but not the substring "distr"*)
Search Z.add Z.mul "add" -"distr".

   