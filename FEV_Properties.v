Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

(*How about this theorem????*)
Theorem feval_eq : forall (e1 e2 : exp), eval e1 e2 = True <-> feval e1 = feval e2.
Proof.
  split.
  - intros. admit.
  - intros. admit.
Admitted.

Theorem feval_correct:
  forall (e1 e2:exp) (ct:ctable), feval e1 ct = Some e2 -> eval e1 e2.
Proof.
  intro. induction e1; intros.
  - simpl in H. injection H. intros. rewrite H0. (* apply eval_context. *) admit.
  - destruct e1 eqn:D.
    + inversion H. rewrite H1. admit.
    + admit.
    + admit.
    + simpl in IHe1. remember (get c ct) as ofs. destruct ofs.
      * remember (snd (fst p)) as fs. remember (combine (List.map fst fs) l) as fes.
        apply eval_field with (fs:=fs) (fes:=fes).
        -- admit.
        -- admit.
        -- admit.
      * simpl in H. rewrite <- Heqofs in H. discriminate.
 (*apply eval_field with (fs:=snd (get c ct)) (fes:=combine (List.map fst fs) l).*)
  - admit.
  - admit.
Admitted.
