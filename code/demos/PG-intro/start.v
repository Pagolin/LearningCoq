Require Export Arith.
Require Export Lia.
Require Export Coq.Lists.List. 
Export ListNotations.

Section Lists0.
  Variable A : Type.

  (* delay processing of this file to show the queue region more clearly *)
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.
  Eval vm_compute in 2^13.

  Lemma append_is_nil : forall(l1 l2 : list A),
      l1 ++ l2 = [] <-> l1 = [] /\ l2 = [].
  Proof using.
    intros l1 l2.
    split.
      intros H.
      apply app_eq_nil in H.
      trivial.
    intros H.
    destruct H.
    subst l1 l2.
    trivial.
  Qed.

  Lemma list_two_step_induction :
    forall(P : list A -> Prop),
      P [] ->
      (forall(a : A), P [a]) ->
      (forall(a b : A)(l : list A), P l -> P (b :: l) -> P (a :: b :: l)) ->
        forall(l : list A), P l.
  Proof using.
    intros P H H0 H1.
    assert (forall(l : list A)(a : A), P l /\ P (a :: l)).
      induction l.
        intros a.
        auto.
      intros b.
      split.
        apply IHl.
      apply H1.
        apply (IHl b).
      apply IHl.
    intros l.
    destruct l.
      trivial.
    apply (H2 _ a).
  Qed.

  (*
     01 - enable tool bar M-x tool-bar-mode
     02 - emacs terminology: frames, windows, buffers, and files
          X11 windows are called frames
          one frame can show multiple windows
          each window shows a buffer
          buffers can be loaded and saved to files

          C-x 1 - delete-other-windows
          C-x 0 - delete-window
          C-x 2 - split-window-below
     03 - explain C-g
     04 - explain regions: locked, queue, editing
     05 - demonstrate strict read-only
          PG->Quick Options->Read Only->Strict
          (customize proof-strict-read-only to t)
     06 - reset strict read-only
     07 - show background coqtop
     08 - comment Eval stuff
     09 - save screen space
          two pane mode: disable PG->Quick Options->Display->Use Three Panes
                         (customize proof-three-window-enable to nil)
          shrink to fit: enable PG->Quick Options->Display->Shrint To Fit
                         (customize proof-shrink-windows-tofit to t)
     10 - make customization permanent : PG->Quick Options->Save
                  C-h v some-variable
     11 - disable splash screen: customize proof-splash-enable to nil
          or increase proof-splash-time to 30
     12 - more screen space
          hide additional subgoals: (customize coq-hide-additional-subgoals to t)
          menu Coq->Settings->Hide Additional Subgoals
     13 - keep orientation with prooftree
     14 - use Coq->OTHER QUERIES->Show ith Goal (C-c C-a C-s)
     15 - show how to move goals to separate frame
          delete goals window
          then do C-x 5 b <ENTER>
          or select goals in different frame or window
     16 - goto firstn.v

   *)
              


End Lists0.
