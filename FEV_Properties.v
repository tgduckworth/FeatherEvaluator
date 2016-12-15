Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Lemma decomp_no_apply:
  forall (e1 e2 e3 e4:fexp), fst (decomp (f_apply e1 e2)) <> f_apply e3 e4.
Proof.
  intro. induction e1; intros.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. discriminate.
  - apply IHe1_1.
Qed.

Lemma apply_rev_args:
  forall (e1 e2 h:fexp) (t:list fexp),
    h::t = rev (snd (decomp (f_apply e1 e2))) -> e2 = h.
Proof.
  intros. simpl in H. rewrite rev_app_distr in H. simpl in H. injection H.
  intros. symmetry. assumption.
Qed.

Lemma decomp_apply_meth:
  forall (e1 e2 eb:fexp) (ps:list fexp) (mn:mname),
    decomp (f_apply e1 e2) = (f_meth eb mn, ps ++ e2::nil) ->
      fexp2exp (f_apply e1 e2) = e_meth (fexp2exp eb) mn (List.map fexp2exp (ps ++ e2::nil)).
Proof.
  intro. induction e1; intros.
  - simpl. discriminate.
  - simpl. discriminate.
  - inversion H. subst. reflexivity.
  - simpl. discriminate.
  - simpl. destruct e1_1 eqn:De1_1.
    + discriminate.
    + discriminate.
    + simpl in *. injection H. intros. subst. injection H. intros.
      rewrite <- H1. simpl. reflexivity.
    + discriminate.
    + injection H. intros. admit.
Admitted.

Lemma decomp_apply_new:
  forall (e1 e2:fexp) (ps:list fexp) (cn:cname),
    decomp (f_apply e1 e2) = (f_new cn, ps) ->
      fexp2exp (f_apply e1 e2) = e_new cn (List.map fexp2exp ps).
Proof.
  intro. induction e1.
  - simpl. discriminate.
  - simpl. discriminate.
  - simpl. discriminate.
  - intros. inversion H. subst. simpl. reflexivity.
  - intros. simpl in H.
Admitted.

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
      * destruct (fst (decomp (f_apply f0_1 f0_2))) eqn:DD.
        --  discriminate.
        --  discriminate.
        --  destruct (snd (decomp (f_apply f0_1 f0_2))) eqn:PS.
            ++  simpl in PS. apply app_eq_nil in PS. destruct PS. discriminate.
            ++  remember (rev (snd (decomp (f_apply f0_1 f0_2)))) as RPS.
                destruct RPS.
                **  simpl in HeqRPS. rewrite rev_app_distr in HeqRPS.
                    symmetry in HeqRPS. apply app_eq_nil in HeqRPS.
                    destruct HeqRPS. discriminate.
                **  apply apply_rev_args in HeqRPS as F0_2. admit.
        --  admit.
        --  apply decomp_no_apply in DD. exfalso. assumption.
    + admit.
Admitted.
