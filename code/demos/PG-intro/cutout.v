Require Export firstn skipn.

Section Lists1.

  Variable A : Type.

  Definition cutout_nth{A : Type}(l : list A)(n : nat) : list A :=
    (firstn n l) ++ (skipn (1 + n) l).

  (* 25 - type "Compute cutout_nth [0;1;2;3;4] 2."
          here with using dabbrev-expand
   *)

  Lemma cutout_nth_cons_0 : 
    forall(a : A)(l : list A), cutout_nth (a :: l) 0 = l.
  Proof using.
    intros a l.
    trivial.
  Qed.

  Lemma cutout_nth_cons_succ :
    forall(a : A)(l : list A)(n : nat), 
      cutout_nth (a :: l) (S n) = a :: cutout_nth l n.
  Proof using.
    intros a l n.
    trivial.
  Qed.

  (* 26 - start this proof *)
  Lemma cutout_nth_append_left :
    forall(l1 l2 : list A)(n : nat),
      n < length l1 ->
        cutout_nth (l1 ++ l2) n = (cutout_nth l1 n) ++ l2.
  (* 27 type Proof using. *)
    (* 28 - configure electric terminator
       PG->Quick Options->Processing->Electric Terminator
       (proof-electric-terminator-enable t)
     *)
    (* 29 add intros *)
    (* 30 unfold cutout_nth *)
    (* 31 search for suitable firstn lemma
       Coq->OTHER QUERIES->Search
       C-c C-a C-a (firstn _ (_ ++ _ ))

       nothing suitable, add our own in firstn.v
     *)

    
    (* 34 reduce time to process to this point again:
       PG->Quick Options->Processing->Omit Proofs
       customize proof-omit-proofs-option to t
     *)


  (* 35 continue proof
   *
   *   rewrite firstn_append_left; trivial.
   *     rewrite skipn_append_left.
   *       apply app_assoc.
   *     auto.
   *   auto with arith.
   * Qed.
   *)

(* 36 demonstrate TAGS

   using perl script coqtags from PG/coq/coqtags

   xref-find-definitions is on M-.
   Edit->Go To->Find Definition


   xref-pop-marker-stack is on M-,
   Edit->Go To->Back (only visible when stack nonempty)
 *)

End Lists1.
