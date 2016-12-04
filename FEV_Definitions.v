Require Import Metatheory.
Require Import FJ_Definitions.

Fixpoint feval (e:exp) (ct: ctable) : option exp :=
  match e with
  | e_field (e_new C es) f =>
    match (get C ct) with
    | Some (_, fs, _) => get f (combine (List.map fst fs) es)
    | None => None
    end   (**R-FIELD**)
  | e_meth (e_new C es) m ds =>
    match (get C ct) with
    | Some (_, _, ms) => 
      match (get m ms) with
      | Some (_,en,ex) => Some (subst_exp ((this,(e_new C es))::(combine (List.map fst en) ds)) ex)
      | None => None
      end
    | None => None
    end (**R-INVK**)
  | e_field e f =>
    match (feval e ct) with
    | Some ex => Some (e_field ex f)
    | None => None
    end      (**RC-FIELD**)
  | e_meth e m es =>
    match (feval e ct) with
    | Some ex => Some (e_meth ex m es)
    | None => None
    end    (**RC_INVK-RECV**)
  | e_new c es => Some (e_new c es) 
  | e_var v => Some (e_var v)
  end.
