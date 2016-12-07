Require Import Metatheory.
Require Import FJ_Definitions.

Fixpoint feval (e:exp) (ct:ctable) : option exp :=
  match e with
  | e_field (e_new C es) f =>
    match (get C ct) with
    | Some (_, fs, _) => get f (combine (List.map fst fs) es) (* R-FIELD *)
    | None => None (* Class not found *)
    end
  | e_meth (e_new C es) m ds =>
    match (get C ct) with
    | Some (_, _, ms) =>
      match (get m ms) with
      | Some (_,en,ex) => Some (subst_exp ((this,(e_new C es))::(combine (List.map fst en) ds)) ex) (* R-INVK *)
      | None => None (* Insert case for inheritance here *)
      end
    | None => None (* Class not found *)
    end
  | e_field e f =>
    match (feval e ct) with
    | Some e' => Some (e_field e' f) (* RC-FIELD *)
    | None => None (* Field access on an expression that isn't an object *)
    end            (* but cannot be reduced produces nothing *)
  | e_meth e m es =>
    match (feval e ct) with
    | Some e' => Some (e_meth e' m es) (* RC-INVK-RECV *)
    | None =>
      match lfeval es ct with
      | Some es' => Some (e_meth e m es') (* RC-INVK-ARG *)
      | None => None (* Method invocation on an expression that isn't an *)
      end            (* object but cannot be reduced produces nothing *)
    end
  | e_new c es =>
    match lfeval es ct with
    | Some es' => Some (e_new c es') (* RC-NEW-ARG *)
    | None => None (* If an object's argument expressions do not reduce, then *)
    end            (* the expression as a whole does not reduce *)
  | e_var _ => None (* Catch-all for variables, which do not step to anything *)
  end

with lfeval (es:list exp) (ct:ctable) : option (list exp) :=
  match es with
  | e::et =>
    match feval e ct with
    | Some e' => Some (e'::et) (* Head steps to something *)
    | None =>
      match lfeval et ct with
      | Some et' => Some (e::et') (* Tail steps to something *)
      | None => None (* List does not step to anything *)
      end
    end
  | nil => None (* Base case: empty list steps to nothing *)
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