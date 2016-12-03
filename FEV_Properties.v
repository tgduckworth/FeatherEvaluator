Require Import FJ_Definitions.

Theorem feval_correct:
  forall (e1 e2:exp) (ct:ctable), feval e1 ct = Some e2 -> eval e1 e2.
Proof.
  intro. induction e1; intros.
  - simpl in H. injection H. intros. rewrite H0. (* apply eval_context. *) admit.
  - 
  -
  -
Admitted.
