(* A tutorial on coqs module system *)

(* The most common Module definition *)
(* 'Module' <module_name> '.' *)
(* start an *interactive* definition of a module *)
Module some_name.
  Definition n := 4.

  Notation "'idk'" := n (only parsing).
  (* interactive definition has to be ended with an *)
  (* 'End' <same_name> '.' *)
End some_name.

(* Defnitions are namespaced within the name of the module *)
(* They cannot be accessed directly *)

Fail Check n. (* reference n was not found *)
Succeed Check some_name.n.

(* to access module definition without prefix -> import them

partial import by specifying '('')' with selection
*)

Import (notations) some_name.
Fail Check n.
Check idk.

Import some_name.
Check n.

(* This can also be shortened by putting the Import
directly in the module command *)

Module Import imported_module.
  Definition imported_definition := 5.
End imported_module.

Check imported_definition.


(* Selective import *)
Module X.
  Module Y.
    Definition one := 1.
    Definition two := 2.
  End Y.
  Module Z.
    Definition three := 3.
  End Z.
  Definition four := 4.
End X.

Import X(Y.one, Z.three, four).
Check Y.one.
Check Z.three.
Check four.
Fail Check Y.two.


(*
A module signature

Used to define which names a module should provide

Defined with 'Module Type'
*)
Module Type Module_sig_a.
  Parameter a_type : Type.

  Axiom a_exists : exists x : a_type, True.
End Module_sig_a.
Module Type Module_sig_b.
  Parameter b_type : Type.

  Axiom b_exists : exists x : b_type, True.
End Module_sig_b.

(* A modul implementing this signature *)
Module Implementing_sig <: Module_sig_a <: Module_sig_b.

  (* cannot end module without providing 'some_type' *)
  Fail End Implementing_sig.

  (* for some reason that I do not fully
    understand the parameeter cannot be
    directly implemented by an 'Inductive' *)
  Inductive some_type := t1 | t2 | t3.
  Definition a_type := some_type.
  Definition b_type := some_type.

  Lemma a_exists : exists x : a_type, True.
    eexists; [exact t1 | exact I].
  Defined.
  Lemma b_exists : exists x : b_type, True.
    eexists; [exact t2 | exact I].
  Defined.
End Implementing_sig.

(*
A module functor - a module depending on a parameter

parameters can only have a 'Module Type' as type
*)
Module Functor (arg1 : Module_sig_a) (Import arg2 : Module_sig_b).
  (* typically the argument is directly imported
  to refer to the defined symbols directly *)
  (* this can also be declared directly in the
  module command *)
  Import arg1.

  Check a_type.

  (* definitions and lemmas in this module
  can depend on the given modul argument *)
  Definition some_f : a_type -> nat := fun x => 5.

  Definition ab_type : Type := a_type * b_type.
End Functor.

(* Supplying a functor with a modul argument
returns a modul *)
Module Functor_Instance := Functor Implementing_sig Implementing_sig.
Compute Functor_Instance.ab_type.
