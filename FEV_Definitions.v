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
    | e1 => e1 (* This case should never occur; it's malformed *)
    end
  end.

Fixpoint decomp (e:fexp) : fexp * list fexp :=
  match e with
  | f_apply e1 e2 => (fst (app_decomp e1), e2::(snd (app_decomp e1)))
  | e => (e, nil)
  end.

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  match e with
  | f_field e f =>
    match decomp e with
    | (e, nil) => (* note sure what to do here *)
    | (e', es) => (* probably a match statement on e' *)
    end
  end.

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  match e with
  | f_field (f_apply (f_new C) al) f =>
    match (get C ct) with
    | Some (_, fs, _) =>
      match fexp2list al with
      | Some es => get f (combine (List.map fst fs) es) (* R-FIELD *)
      | None => None (* Arguments could not be made into a list *)
    | None => None (* Class not found *)
    end
  | f_apply (f_meth (f_new C) m) al =>
    match (get C ct) with
    | Some (_, _, ms) =>
      match (get m ms) with
      | Some (_,en,ex) => Some (subst_exp ((this,(e_new C al))::(combine (List.map fst en) al)) ex) (* R-INVK *)
      | None => None (* Insert case for inheritance here *)
      end
    | None => None (* Class not found *)
    end
  | f_field e f =>
    match (feval e ct) with
    | Some e' => Some (f_field e' f) (* RC-FIELD *)
    | None => None (* Field access on an expression that isn't an object *)
    end            (* but cannot be reduced produces nothing *)
  | f_apply (f_meth e m) al =>
    match (feval e ct) with
    | Some e' => Some (f_apply (f_meth e' m) al) (* RC-INVK-RECV *)
    | None =>
      match feval al ct with
      | Some al' => Some (f_apply (f_meth e m) al') (* RC-INVK-ARG *)
      | None => None (* Method invocation on an expression that isn't an *)
      end            (* object but cannot be reduced produces nothing *)
    end
  | f_apply (f_new C) al =>
    match feval al ct with
    | Some al' => Some (f_apply (f_new C) al') (* RC-NEW-ARG *)
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