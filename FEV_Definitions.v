Require Import Metatheory.
Require Import FJ_Definitions.

Inductive fexp : Set :=
| f_var : var -> fexp
| f_field : fexp -> fname -> fexp
| f_meth : fexp -> mname -> fexp
| f_new : cname -> fexp
| f_apply : fexp -> fexp -> fexp.

Fixpoint fexp2exp (e:fexp) : exp :=
  match e with
  | f_var v => e_var v
  | f_field e fn => e_field (fexp2exp e) fn
  | f_meth e mn => e_meth (fexp2exp e) mn nil (* Method 'base' *)
  | f_new cn => e_new cn nil                  (* New 'base' *)
  | f_apply e1 e2 =>                          (* Method/New application *)
    match fexp2exp e1 with
    | e_new cn al => e_new cn ((fexp2exp e2)::al)
    | e_meth e mn al => e_meth e mn ((fexp2exp e2)::al)
    | e => e (* This case should never occur; it's malformed *)
    end
  end.

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  match e with
  | f_field (f_apply (f_new C) es) f =>
    match (get C ct) with
    | Some (_, fs, _) => get f (combine (List.map fst fs) es) (* R-FIELD *)
    | None => None (* Class not found *)
    end
  | f_apply (f_meth (f_new C) m) ds =>
    match (get C ct) with
    | Some (_, _, ms) =>
      match (get m ms) with
      | Some (_,en,ex) => Some (subst_exp ((this,(e_new C ds))::(combine (List.map fst en) ds)) ex) (* R-INVK *)
      | None => None (* Insert case for inheritance here *)
      end
    | None => None (* Class not found *)
    end
  | f_field e f =>
    match (feval e ct) with
    | Some e' => Some (f_field e' f) (* RC-FIELD *)
    | None => None (* Field access on an expression that isn't an object *)
    end            (* but cannot be reduced produces nothing *)
  | f_apply (f_meth e m) ds =>
    match (feval e ct) with
    | Some e' => Some (f_apply (f_meth e' m) ds) (* RC-INVK-RECV *)
    | None =>
      match feval ds ct with
      | Some ds' => Some (f_apply (f_meth e m) ds') (* RC-INVK-ARG *)
      | None => None (* Method invocation on an expression that isn't an *)
      end            (* object but cannot be reduced produces nothing *)
    end
  | f_apply (f_new C) es =>
    match feval es ct with
    | Some es' => Some (f_apply (f_new C) es') (* RC-NEW-ARG *)
    | None => None (* If an object's argument expressions do not reduce, then *)
    end            (* the expression as a whole does not reduce *)
  | f_var _ => None (* Catch-all for variables, which do not step to anything *)
  end.

Fixpoint teval (e:exp) (ct:ctable) (n:nat) : exp :=
  match n with 
  | S x =>
    match feval e ct with
    | Some e' => teval e' ct x
    | None => e
    end
  | 0 => e
  end.