Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Lemma rev_nil:
  forall (A:Type) (l:list A), rev l = nil -> l = nil.
Proof.
  intros. destruct l.
  - reflexivity.
  - simpl in H. destruct (rev l).
    + simpl in H. inversion H.
    + simpl in H. inversion H.
Qed.

Lemma rev_involutive:
  forall (A:Type) (l:list A),
    rev (rev l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Lemma rev_eq_f:
  forall (A:Type) (l1 l2:list A),
    l1 = l2 -> rev l1 = rev l2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma rev_eq_b:
  forall (A:Type) (l1 l2:list A),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros. apply rev_eq_f in H. rewrite rev_involutive in H.
  rewrite rev_involutive in H. assumption.
Qed.

Lemma rev_eq:
  forall (A:Type) (l1 l2:list A),
    l1 = l2 <-> rev l1 = rev l2.
Proof.
  split.
  - intros. apply rev_eq_f. assumption.
  - intros. apply rev_eq_b. assumption.
Qed.

Lemma rev_app:
  forall (A:Type) (l1 l2 l3 t:list A) (a:A),
    rev l1 = a :: t ->
      l1 ++ l2 = l3 -> (rev t) ++ a :: nil ++ l2 = l3.
Proof.
  intros. remember (a :: t) as l1'. rewrite app_comm_cons. rewrite app_assoc.
  rewrite <- rev_involutive in H. rewrite Heql1' in H. simpl in H.
  rewrite <- rev_eq in H. rewrite H in H0. assumption.
Qed.

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

Lemma decomp_reduce:
  forall (e1 e2 e eb:fexp) (ps:list fexp),
    decomp (f_apply (f_apply e1 e2) e) = (eb, ps ++ e::nil) ->
      e1 <> eb ->
      decomp (f_apply e1 e2) = (eb, ps).
Proof.
  intro. induction e1; intros; simpl in *; injection H; intros.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - apply app_inv_tail in H1. rewrite <- H1. rewrite H2. reflexivity.
Qed.

Lemma decomp_reduce_1:
  forall (e1 e2 e3 e4 eb:fexp) (ps:list fexp),
    decomp (f_apply (f_apply (f_apply e1 e2) e3) e4) = (eb, ps ++ e3::nil ++ e4::nil) ->
      e1 <> eb ->
      decomp (f_apply (f_apply e1 e2) e4) = (eb, ps ++ e4::nil).
Proof.
  intro. induction e1; intros; injection H; intros.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - simpl in *. rewrite H2. rewrite <- app_assoc in H1. simpl in H1.
    apply app_inv_tail in H1. rewrite H1. reflexivity.
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
    + injection H. intros. destruct (rev ps) eqn:DRPS.
      * apply rev_nil in DRPS. rewrite DRPS in H0. simpl in H0.
        rewrite <- app_nil_l in H0. apply app_inv_tail in H0.
        destruct (snd (decomp f1) ++ f2 :: nil).
        --  simpl in H0. inversion H0.
        --  simpl in H0. inversion H0.
      * remember (ps ++ e2 :: nil) as pst.
        apply rev_app with (l1:=ps) (l2:=e2 :: nil) (l3:=pst) in DRPS.
        --  rewrite <- DRPS in H. admit.
            (* need to show that f = e1_2 before apply decomp_reduce_1 in H. *)
        --  symmetry. assumption.
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
  - intros. admit. (* hopefully similar to the above! *)
Admitted.

Theorem feval_sound:
  forall (e1 e2:fexp) (fct:fctable), feval e1 fct = Some e2 -> eval (fexp2exp e1) (fexp2exp e2).
Proof.
  intro. induction e1; intros.
  - simpl in H. discriminate.
  - destruct (feval e1 fct) eqn : A.
    + apply IHe1 in A as H0. simpl in H. rewrite A in H.
      destruct e1 eqn : D.
       * discriminate.
       * injection H. intro. rewrite <- H1. simpl.
         inversion H0.
          -- admit.
          -- admit.
       * injection H. intros. rewrite <- H1. simpl.
         remember (fun (e:exp) => e::nil) as EE''.
         remember (fun (e:exp) => e_meth (fexp2exp f0) m (EE'' e)) as EE'.
         apply eval_context with (EE:=EE') in H0.
            --  subst. admit.
            --  rewrite HeqEE'. apply ec_meth_args. rewrite HeqEE''. apply esc_head.
       * discriminate.
       * admit.
    + simpl in H. admit.
  - simpl in H. destruct (feval e1 fct) eqn:D.
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
    + destruct (feval e1_2 fct).
     * discriminate.
     * destruct (snd (decomp (f_apply e1_1 e1_2))) eqn:DD.
        --  simpl in DD. apply app_eq_nil in DD. destruct DD. discriminate.
        --  destruct (f_apply e1_1 e1_2).
          ++  simpl in H. discriminate.
          ++  destruct (feval e1_2 fct) eqn : B.
              **  discriminate.
              **  discriminate.
          ++ discriminate.
          ++ discriminate.
          ++ admit.
Admitted.
