Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FEV_Definitions.

Theorem feval_sound:
  forall (e1 e2:fexp) (fct:fctable), feval e1 fct = Some e2 -> eval (fexp2exp e1) (fexp2exp e2).
Proof.
  
Admitted.
