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
Notation fmths := (list (mname * (typ * env * fexp))).
Notation fctable := (list (cname * (cname * flds * fmths))).

(* Assumes an ordering such that parents are closer to the nil in fct *)
Fixpoint fmbody (cn:cname) (mn:mname) (fct:fctable) : option (env * fexp) :=
  match fct with
  | (C,(D,_,ms))::t =>
    if C == cn then
      match get mn ms with
      | Some (_, en, ex) => Some (en, ex)
      | None => fmbody D mn t
      end
    else fmbody cn mn t
  | nil => None
  end.

(* Assumes an ordering such that parents are closer to the nil in fct *)
Fixpoint ffields (cn:cname) (fct:fctable) : flds :=
  match fct with
  | (C,(D,fs,_))::t =>
    if C == cn then (ffields D t) ++ fs
    else ffields cn t
  | nil => nil
  end.

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
  | f_apply e1 e2 => (fst (decomp e1), (snd (decomp e1)) ++ e2::nil)
  | e => (e, nil)
  end.

Fixpoint feval (e:fexp) (fct:fctable) : option fexp :=
  match e with
  | f_apply e1 e2 =>
    match feval e2 fct with
    | Some e2' =>
      match e1 with
      | f_var v => None      (* Can't step arguments unless well-formed *)
      | f_field e fn => None
      | e1 => Some (f_apply e1 e2') (* RC-INVK-ARG, RC-NEW-ARG *)
      end
    | None =>
      match feval e1 fct with
      | Some e1' => Some (f_apply e1' e2) (* RC-INVK-RECV *)
      | None =>
        let (eb, ps) := decomp e in
          match eb with
          | f_meth em mn =>
            match decomp em with
            | (em, nil) => None (* Method call on non-object *)
            | (emb, emps) =>
              match emb with
              | f_new cn =>
                match fmbody cn mn fct with
                | Some (en, ex) => Some (subst_fexp ((this, em)::(combine (List.map fst en) ps)) ex) (* R-INVK *)
                | None => None (* No such method in the hierarchy *)
                end
              | emb => None (* Method call on application to non-object *)
              end
            end
          | eb => None (* No other simplifications can be made *)
          end
      end
    end
  | f_field e fn =>
    match e with
    | f_apply e1 e2 =>
      let (eb, ps) := decomp (f_apply e1 e2) in
        match eb with
        | f_new cn =>
          match ffields cn fct with
          | nil => None (* Class not found, or no fields *)
          | fs => get fn (combine (List.map fst fs) ps) (* R-FIELD *)
          end
        | eb =>
          match feval e fct with
          | Some e' => Some (f_field e' fn) (* RC-FIELD *)
          | None => None (* Unable to step subexpression of field access *)
          end
        end
    | e =>
      match feval e fct with
      | Some e' => Some (f_field e' fn) (* RC-FIELD *)
      | None => None (* Unable to step subexpression of field access *)
      end
    end
  | f_meth e mn =>
    match feval e fct with
    | Some e' => Some (f_meth e' mn) (* RC-INVK-RECV *)
    | None => None (* If the inner expression can't be stepped, nothing can *)
    end
  | f_new cn => None (* Basic class instantiations never step *)
  | f_var v => None (* Variables never step *)
  end.

Fixpoint teval (e:fexp) (fct:fctable) (n:nat) : fexp :=
  match n with 
  | S x =>
    match feval e fct with
    | Some e' => teval e' fct x
    | None => e
    end
  | 0 => e
  end.