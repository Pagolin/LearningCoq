Require Export start.

Section Lists0.
  Variable A : Type.

  Compute (firstn 2 [1;2;3;4;5]).

  Lemma length_firstn_less :
    forall(l : list A)(n : nat),
      n <= length l ->
        length (firstn n l) = n.
  Proof using.
    intros l n H.
    rewrite firstn_lengt.
    apply min_l.
    trivial.
  Qed.
  
(*
  17 - do 'make deps' and show dependencies.pdf
  18 - try to process this file - abort on retract question
  19 - configure auto retract
       PG->Quick Options->Deactivate Action->Retract
       (proof-auto-action-when-deactivating-scripting 'retract)
       maybe save to make this permanent
  20 - try again to process this file
  21 - configure auto compilation M-x customize-group coq-auto-compile
       - set Coq Compile Before Require
             menu Coq->Auto Compilation->Compile Before Require
             (coq-compile-before-require t)
       - set Coq Compile Auto Save
             menu Coq->Auto Compilation->Auto Save->Autosave coq buffers
             (coq-compile-auto-save 'save-coq)
       - set Coq Compile Vos to -vos and no -vok
             menu Coq->Auto Compilation->vos compilation->use -vos, no -vok
             (coq-compile-vos 'vos)
       - show keep going (is set by default)
             menu Coq->Auto Compilation->Keep going
             (coq-compile-keep-going t)
       - show Coq Lock Ancestors
       - show Coq Max Background Compilation Jobs
       - save all
  22 - Explain C-c C-c (proof-interrupt-process), show menu
  23 - explain firstn with Compute
  24 - goto skipn.v, show Compute there, then goto cutout.v
 *)



  (* 32 add "Lemma firstn_append_left :"

       What did we want to proof?
       Go back and store goal / also show prooftree goal display
       Coq->Store Goal
       C-c C-a g
   *)


(* 33 add the lemma statement and the proof below
      - search for Nat.sub_0_le, explain proj2
      - then go back to cutout.v
 *)
  
  (*
   *   forall(l1 l2 : list A)(n : nat),
   *     n <= length l1 ->
   *       firstn n (l1 ++ l2) = firstn n l1.
   * Proof using.
   *   intros l1 l2 n nle.
   *   rewrite firstn_app.
   *   rewrite (proj2 (Nat.sub_0_le _ _)); trivial.
   *   rewrite firstn_O.
   *   apply app_nil_r.
   * Qed.
   *)

End Lists0.

  
