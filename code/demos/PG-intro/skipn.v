Require Export start.

Section Lists0.
  Variable A : Type.

  Compute (skipn 2 [1;2;3;4;5]).

  Lemma skipn_append_left : forall(l1 l2 : list A)(n : nat),
    n <= length l1 -> skipn n (l1 ++ l2) = (skipn n l1) ++ l2.
  Proof using.
    intros l1 l2 n nle.
    rewrite skipn_app.
    rewrite (proj2 (Nat.sub_0_le _ _)); trivial.
  Qed.

End Lists0.
