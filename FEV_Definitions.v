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

Notation fbenv := (list (var * fexp)).

Fixpoint subst_fexp (E : fbenv) (e : fexp) {struct e} : fexp :=
    match e with
    | f_var v =>
        match get v E with
        | Some e' => e'
        | None => f_var v
        end
    | f_field e0 fn => f_field (subst_fexp E e0) fn
    | f_meth e0 mn => f_meth (subst_fexp E e0) mn
    | f_new C => f_new C
    | f_apply e1 e2 => f_apply (subst_fexp E e1) (subst_fexp E e2)
    end.

Fixpoint decomp (e:fexp) : fexp * list fexp :=
  match e with
  | f_apply e1 e2 => (fst (decomp e1), e2::(snd (decomp e1)))
  | e => (e, nil)
  end.

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  match e with
  | f_apply e1 e2 =>             (* If the expression is an application we    *)
    match feval e2 ct with       (* have to both simplify arguments AND       *)
    | Some e2' => f_apply e1 e2' (* check for the conditions for method calls *)
    | None =>                    (* since those can be invoked.               *)
      match feval e1 ct with
      | Some e1' => f_apply e1' e2
      | None =>
        match decomp e with
        | (eb, nil) => None (* Shouldn't happen since e is f_apply *)
        | (eb, ps) =>
          match eb with
          | f_meth em mn =>
            match decomp em with
            | (em, nil) => None (* Method call on non-object *)
            | (emb, emps) =>
              match emb with
              | f_new cn =>
                match get cn ct with
                | Some (_, _, ms) =>
                  match get mn ms with
                  | Some (_, en, ex) => Some (subst_fexp ((this, em)::(combine (List.map fst en) ps)) ex) (* R-INVK *)
                  | None => None (* TODO: Case for inheritance *)
                  end
                | None => None (* Class not found *)
                end
              | emb => None (* Method call on application to non-object *)
              end
            end
          | eb => None (* No other simplifications can be made *)
          end
        end
      end
    end
  | e =>
    match decomp e with
    | (e, nil) =>
      match e with
      | f_field e fn =>
        match decomp e with
        | (e1, nil) =>
          match feval e1 ct with
          | Some e1' => f_field e1' fn (* RC-FIELD *)
          | None => None (* Unable to to step subexpression of field access *)
          end
        | (e1, ps) =>
          match e1 with
          | f_new cn =>
            match get cn ct with
            | Some (_, fs, _) => get fn (combine (List.map fst fs) ps) (* R-FIELD *)
            | None => None (* Class not found *)
            end
          | e1 => None (* TODO?*)
          end
        end
      | f_meth e mn => None (* TODO *)
      | f_new cn => None (* TODO *)
      | f_var v => None (* TODO *)
      | f_apply e1 e2 => None (* Should not happen by definition of decomp *)
      end
    | (e, ps) =>
      match e with
      | f_meth em mn => None (* TODO *)
      | f_new cn => None (* TODO *)
      | f_field e fn => None (* TODO *)
      | f_var v => None (* TODO *)
      | f_apply e1 e2 => None (* Should not happen by definition of decomp *)
      end
    end
  end.

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  .

Fixpoint feval (e:fexp) (ct:ctable) : option fexp :=
  match e with
  | f_field e fn =>
    match decomp e with
    | (e, nil) => (* Field access on non-apply *)
      match feval e ct with
      | Some e' => Some (f_field e' fn) (* RC-FIELD *)
      | None => None (* Field access on a non-apply that doesn't simplify *)
      end
    | (eb, fes) => (* Field access on apply *)
      match eb with
      | f_new cn => (* Field access on an instantiation *)
        match (get cn ct) with
        | Some (_, fs, _) => get fn (combine (List.map fst fs) fes) (* R-FIELD *)
        | None => None (* Class not found *)
        end
      | eb =>                 (* On anything else we just try to step the *)
        match feval e ct with (* field subexpression, as above *)
        | Some e' => Some (f_field e' fn) (* RC-FIELD *)
        | None => None (* The expression being accessed doesn't step *)
        end
      end
    end
  | f_apply e1 e2 =>
    match feval e2 ct with
    | Some e2' => Some (f_apply e1 e2')
    | None =>
      match feval e1 ct with
      | Some e1' => Some (f_apply e1' e2)
      | None =>
        match decomp e1 with
        | (eb, fes) =>
          match feval eb ct with
          | Some 
          |
          end
        | (e1, nil) => None
        end
      end
    end
  | f_var _ => None
  | f_meth e mn =>
    match feval e ct with
    | Some e' => Some (f_meth e' mn)
    | None => None
    end
  | f_new cn => None
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