
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

(** printing \in %\ensuremath{\in}% *)
(** printing \notin %\ensuremath{\notin}% *)
(** printing == %\ensuremath{\doteq}% *)

(** This library contains the actual Featherweight Java language definition.
    The definition is divided up between syntax, auxiliaries, evaluation and
    typing. *)

Require Import Metatheory.

(** * Syntax *)

(** ** Lexical categories *)

(** Names of variables, fields, methods and classes are atoms (their equality
    is decidable). *)

Definition var := atom.
Definition fname := atom.
Definition mname := atom.
Definition cname := atom.

(** The names [this] and [Object] are predefined. We simply assume that these
    names exist. *)

(**Parameter this : var.
Parameter Object : cname.**)
Definition this : var := 0.
Definition Object : cname := 1.

(** ** Type and term expressions *)

(** Class names are the only form of types. **)

Definition typ := cname.

(** The expression forms are variable reference, field get, method invocation
    and object creation. *)

Inductive exp : Set :=
| e_var : var -> exp
| e_field : exp -> fname -> exp
| e_meth : exp -> mname -> list exp -> exp
| e_new : cname -> list exp -> exp.

(** ** Environments and class tables *)

(** An [env] declares a number of variables and their types. A [benv] binds
    variables to expressions. *)

Notation env := (list (var * typ)).
Notation benv := (list (var * exp)).

(** [flds] and [mths] map the names of fields and methods to their
    definitions. *)

Notation flds := (list (fname * typ)).
Notation mths := (list (mname * (typ * env * exp))).

(** [ctable] maps the names of classes to their definitions. A class definition
    consists of a parent class and a number of fields and methods. *)

Notation ctable := (list (cname * (cname * flds * mths))).

(** We assume a fixed class table [CT]. *)

Parameter CT : ctable.

(** * Auxiliaries *)

(** ** Field and method lookup *)

(** [field C f t] holds if a field named [f] with type [t] is defined for class
    [C] in the class hierarchy. *)

Inductive fields : cname -> flds -> Prop :=
| fields_obj : fields Object nil
| fields_other : forall C D fs fs' ms, 
    binds C (D,fs,ms) CT ->
    fields D fs' ->
    fields C (fs'++fs).

Hint Constructors fields.

Definition field (C : cname) (f : fname) (t : typ) : Prop :=
    exists2 fs, fields C fs & binds f t fs.

Hint Unfold field.

(** [method C m mdecl] holds if a method named [m] with declaration [mdecl] is
    defined for class [C] in the class hierarchy. *)

Inductive method : cname -> mname -> typ * env * exp -> Prop :=
| method_this : forall C D fs ms m mdecl,
    binds C (D,fs,ms) CT ->
    binds m mdecl ms ->
    method C m mdecl
| method_super : forall C D fs ms m mdecl,
    binds C (D,fs,ms) CT ->
    no_binds m ms ->
    method D m mdecl ->
    method C m mdecl.

Hint Constructors method.

(** ** Term substitution *)

(** [subst_exp E e] returns the term expression [e] where any occurrences of
    bound variables have been replaced by their bindings in environment [E]. *)

Fixpoint subst_exp (E : benv) (e : exp) {struct e} : exp :=
    match e with
    | e_var v =>
        match get v E with
        | Some e' => e'
        | None => e_var v
        end
    | e_field e0 f => e_field (subst_exp E e0) f
    | e_meth e0 m es => e_meth (subst_exp E e0) m (List.map (subst_exp E) es)
    | e_new C es => e_new C (List.map (subst_exp E) es)
    end.

(** * Evaluation *)

(** ** Evaluation contexts *)

(** We model evaluation contexts as functions of type [exp -> exp].
    [exp_context EE] holds if [EE] is an evaluation context. Basically, any
    subexpression of an expression is an evaluation context. **)

Inductive exps_context : (exp -> list exp) -> Prop :=
| esc_head : forall es,
    exps_context (fun e => e::es)
| esc_tail : forall e EE,
    exps_context EE ->
    exps_context (fun e0 => e::(EE e0)).

Inductive exp_context : (exp -> exp) -> Prop :=
| ec_field_arg0 : forall f,
    exp_context (fun e0 => e_field e0 f)
| ec_meth_arg0 : forall m es,
    exp_context (fun e0 => e_meth e0 m es)
| ec_meth_args : forall m e0 EE,
    exps_context EE ->
    exp_context (fun e => e_meth e0 m (EE e))
| ec_new_args : forall C EE,
    exps_context EE ->
    exp_context (fun e => e_new C (EE e)).

Hint Constructors exp_context exps_context.

(** ** Evaluation *)

(** [eval e e'] holds when term expression [e] reduces to [e'] in one step. *)

Inductive eval : exp -> exp -> Prop :=
| eval_field : forall C fs es f e fes,
    fields C fs ->
    env_zip fs es fes ->
    binds f e fes ->
    eval (e_field (e_new C es) f) e
| eval_meth : forall C m t E e es ves es0,
    method C m (t,E,e) ->
    env_zip E es ves ->
    eval (e_meth (e_new C es0) m es) (subst_exp ((this,(e_new C es0))::ves) e)
| eval_context : forall EE e e',
    eval e e' ->
    exp_context EE ->
    eval (EE e) (EE e').

Hint Constructors eval.
(* Help Coq to eapply eval_context rule ("Meta cannot occur in evar body") *)
Hint Extern 2 (eval (e_field _ ?f) _) => eapply (eval_context (fun e0 => e_field e0 f)).
Hint Extern 2 (eval (e_meth _ ?m ?es) _) => eapply (eval_context (fun e0 => e_meth e0 m es)).
Hint Extern 2 (eval (e_meth ?e0 ?m (?EE _)) _) => eapply (eval_context (fun e => e_meth e0 m (EE e))).
Hint Extern 2 (eval (e_new ?C (?EE _)) _) => eapply (eval_context (fun e => e_new C (EE e))).

(** * Typing *)

(** ** Well-formed types *)

(** [ok_type t] holds when [t] is a well-formed type. *)

Inductive ok_type : typ -> Prop :=
| ok_obj: ok_type Object
| ok_in_ct: forall t, t \in dom CT -> ok_type t.

Hint Constructors ok_type.

(** ** Subtyping *)

(** [extends C D] holds if [C] is a direct subclass of [D]. *)

Definition extends (C D : cname) : Prop :=
    exists fs, exists ms, binds C (D,fs,ms) CT.

Hint Unfold extends.

(** [sub s u] holds if [s] is a subtype of [u]. The subtype relation is the
    reflexive, transitive closure of the direct subclass relation. *)

Inductive sub : typ -> typ -> Prop :=
| sub_refl : forall t, sub t t
| sub_trans : forall t1 t2 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3
| sub_extends : forall C D, extends C D -> sub C D.

Hint Constructors sub.

(** ** Term expression typing *)

(** [typing E e t] holds when expression [e] has type [t] in environment [E].
    [wide_typing E e t] holds when [e] has a subtype of [t]. *)

Inductive typing : env -> exp -> typ -> Prop :=
| t_var : forall v t E,
    ok E ->
    binds v t E ->
    typing E (e_var v) t
| t_field : forall E e0 t0 t f,
    typing E e0 t0 ->
    field t0 f t ->
    typing E (e_field e0 f) t
| t_meth : forall E E0 e0 b t0 t m es,
    typing E e0 t0 ->
    method t0 m (t,E0,b) ->
    wide_typings E es (imgs E0) ->
    typing E (e_meth e0 m es) t
| t_new : forall E C fs es,
    fields C fs ->
    wide_typings E es (imgs fs) ->
    typing E (e_new C es) C

with wide_typing : env -> exp -> typ -> Prop :=
| wt_sub : forall E e t t',
    typing E e t -> sub t t' -> wide_typing E e t'

with wide_typings : env -> list exp -> list typ -> Prop :=
| wts_nil : forall E,
    ok E ->
    wide_typings E nil nil
| wts_cons : forall E E0 es e t,
    wide_typings E es E0 ->
    wide_typing E e t ->
    wide_typings E (e::es) (t::E0).

Hint Constructors typing wide_typing wide_typings.

(** ** Declaration typing *)

(** [ok_meth C D m t E e] holds when [(t, E, e)] is a valid method declaration
    for method [m] in class [C] with parent [D]. *)

Definition can_override (D: cname) (m: mname) (t: typ) (E: env) : Prop :=
    forall t' E' e, method D m (t',E',e) -> sub t t' /\ imgs E = imgs E'.

Hint Unfold can_override.

Definition ok_meth (C D: cname) (m: mname) (t: typ) (E: env) (e: exp) : Prop :=
    can_override D m t E /\ wide_typing ((this,C)::E) e t.

Hint Unfold ok_meth.

(** [ok_class C D fs ms] holds when it is valid to define class [C] with parent
    [D], fields [fs] and methods [ms]. *)

Definition ok_meth' (C D: cname) (m : mname) (v : typ * env * exp) : Prop :=
    match v with (t,E,e) => ok_meth C D m t E e end.

Definition ok_class (C: cname) (D: cname) (fs: flds) (ms: mths) : Prop :=
    (forall fs', fields D fs' -> ok (fs' ++ fs)) /\
    ok ms /\
    forall_env (ok_meth' C D) ms.

Hint Unfold ok_class.

(** [ok_ctable ct] holds when [ct] is a well-formed class table. *)

Definition ok_class' (C: cname) (v : cname * flds * mths) : Prop :=
    match v with (D,flds,mths) => ok_class C D flds mths end.

Definition ok_ctable ct := ok ct /\ forall_env ok_class' ct.

Hint Unfold ok_ctable.

(** * Properties *)

(** We conclude the definition of the calculus with a definition of the safety
    properties that are proven in the other parts of the development. *)

(** [value e] holds when the term expression [e] represents a value. Values are
    terms that consist only of [e_new] expressions. *)

Inductive value : exp -> Prop :=
| value_new : forall cn es,
    (forall e, In e es -> value e) -> value (e_new cn es).

Hint Constructors value.

(** The following module defines the hypotheses of the safety argument. We
    assume that [Object] is not defined in the class table [CT] and that class
    table [CT] is well-formed. *)

Module Type Hyps.
    Parameter ct_noobj: Object \notin dom CT.
    Parameter ok_ct: ok_ctable CT.
End Hyps.

(** Safety of the language may be demonstrated through an implementation 
    of the following module type: given the above hypotheses, it provides the
    properties of preservation and progress. *)

Module Type Safety (H: Hyps).
    Parameter preservation: forall E e e' t,
        typing E e t ->
        eval e e' ->
        wide_typing E e' t.

    Parameter progress: forall e t,
        typing nil e t ->
        value e \/ (exists e', eval e e').
End Safety.
