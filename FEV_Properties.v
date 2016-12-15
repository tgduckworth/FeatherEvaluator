Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Theorem decomp_no_apply:
  forall (e1 e2 e3 e4:fexp), fst (decomp (f_apply e1 e2)) <> f_apply e3 e4.
Proof.
  intro. induction e1; intros.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. discriminate.
  - apply IHe1_1.
Qed.

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
  - destruct (feval e1_2 fct) eqn:Fe1_2.
    + apply IHe1_2 in Fe1_2 as H0. simpl in H. rewrite Fe1_2 in H.
      destruct e1_1 eqn:De1_1.
      * discriminate.
      * discriminate.
      * injection H. intro. rewrite <- H1. simpl.
        remember (fun (e:exp) => e::nil) as EE''.
        remember (fun (e:exp) => e_meth (fexp2exp f0) m (EE'' e)) as EE'.
        apply eval_context with (EE:=EE') in H0.
        --  subst. assumption.
        --  rewrite HeqEE'. apply ec_meth_args. rewrite HeqEE''. apply esc_head.
      * injection H. intro. rewrite <- H1. simpl.
        remember (fun (e:exp) => e::nil) as EE''.
        remember (fun (e:exp) => e_new c (EE'' e)) as EE'.
        apply eval_context with (EE:=EE') in H0.
        --  subst. assumption.
        --  rewrite HeqEE'. apply ec_new_args. rewrite HeqEE''. apply esc_head.
      * subst. destruct (fst (decomp (f_apply f0_1 f0_2))) eqn:DD.
        --  discriminate.
        --  discriminate.
        --  admit.
        --  admit.
        --  apply decomp_no_apply in DD. exfalso. assumption.
    + admit.
Admitted.
