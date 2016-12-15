Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Theorem feval_sound:
  forall (e1 e2:fexp) (ct:fctable), feval e1 ct = Some e2 -> eval (fexp2exp e1) (fexp2exp e2).
Proof.
  intro. induction e1; intros.
  - simpl in H. discriminate.
  - destruct e1 eqn:D.
    + inversion H.
    + admit.
    + admit.
    + simpl in H. discriminate.
    + admit.
  - simpl in *. destruct (feval e1 ct).
    + injection H. intro. rewrite <- H0. simpl.
    + discriminate.
  - simpl in H. discriminate.
  - admit.
Admitted.
