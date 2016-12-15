Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Theorem feval_sound:
  forall (e1 e2:fexp) (fct:fctable), feval e1 fct = Some e2 -> eval (fexp2exp e1) (fexp2exp e2).
Proof.
  intro. induction e1; intros.
  - simpl in H. discriminate.
  - destruct e1 eqn:D.
    + inversion H.
    + admit.
    + admit.
    + simpl in H. discriminate.
    + admit.
  - simpl in *. destruct (feval e1 fct) eqn:D.
    + apply IHe1 in D. remember (fun (e:exp) => e_meth e m nil) as EE'.
      apply eval_context with (EE:=EE') in D.
      * rewrite HeqEE' in D. injection H. intro. rewrite <- H0. simpl.
        assumption.
      * rewrite HeqEE'. apply ec_meth_arg0.
    + discriminate.
  - simpl in H. discriminate.
  - admit.
Admitted.
