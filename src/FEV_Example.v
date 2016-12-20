Require Import Atom.
Require Import FJ_Definitions.
Require Import FEV_Definitions.
Require Import List.

Definition C : atom := 2.
Definition D : atom := 3.
Definition Pair : atom := 4.
Definition setFst : atom := 5.
Definition newFst : atom := 6.
Definition myFst : atom := 7.
Definition mySnd : atom := 8.
Definition myThr : atom := 9.
Definition E : atom := 10.
Definition PairC : atom := 11.

(* PARENTS AFTER CHILDREN *)
Definition ct2 : fctable := (
    (C,(Object,nil,nil))
  ::(D,(Object,nil,nil))
  ::(PairC,(
      Pair,
      ((myThr, Object) :: nil),
      nil
    ))
  ::(Pair,(
      Object,
      ((myFst, Object) :: (mySnd, Object) :: nil),
      (
        (setFst,
         (
          Pair,
          (newFst, Object) :: nil,
          f_apply (f_apply (f_new Pair) (f_var newFst)) (f_field (f_var this) mySnd)
         )
        )
        :: nil 
      )
    ))
  :: nil).

(* Arguments written in reverse order: last ones towards the inside *)
Definition myfexp : fexp := f_field (f_apply (f_apply (f_apply (f_new PairC) (f_new E)) (f_new C)) (f_new C)) myThr.

Eval compute in feval myfexp ct2.
Eval compute in teval myfexp ct2 100.

Definition myfexp2 : fexp := f_apply (f_meth (  f_apply (f_apply (f_new Pair) (f_new C)) (f_new D)   ) setFst) (f_new E).

Eval compute in feval myfexp2 ct2.
(** Something is wrong... **)
(** Eval compute in teval myfexp2 ct2 2. **)

(**
OLD IMPLEMENTATION EXAMPLES BELOW
---
Old list-based arguments implementation not compatible with new function-based arguments implementation
**)
(**
Definition ct : fctable := (
    (C,(Object,nil,nil))
  ::(D,(Object,nil,nil))
  ::(Pair,(
      Object,
      ((myFst, Object) :: (mySnd, Object) :: nil),
      (
        (setFst,
         (
          Pair,
          (newFst, Object) :: nil,
          e_new Pair (e_var newFst :: e_field (e_var this) mySnd :: nil)
         )
        )
        :: nil 
      )
    ))
  :: nil).
Definition myexp : exp := (e_field (e_new Pair ((e_new C nil)::(e_new D nil)::nil)) mySnd).
Definition myexp2 : exp := (e_meth (e_new Pair ((e_new C nil)::(e_new D nil)::nil)) setFst ((e_new C nil)::nil)).
Eval compute in feval myexp ct.
Eval compute in feval myexp2 ct.
Eval compute in match feval myexp2 ct with | Some (e_new c (H1::H2::T)) => feval H2 ct | _ => None end.
Definition myexp3 : exp := (
  e_field
    (e_meth
      (e_field
        (e_new Pair (
          (e_new Pair
            ((e_new C nil)
             ::(e_new D nil)::nil)
          )
          ::(e_new C nil)::nil)
        )
      myFst)
      setFst
      ((e_new D nil)::nil)
    )
  mySnd
).
Definition s0 := Some myexp3.
Definition s1 := match s0 with Some e => feval e ct | None => None end.
Definition s2 := match s1 with Some e => feval e ct | None => None end.
Definition s3 := match s2 with Some e => feval e ct | None => None end.
Definition s4 := match s3 with Some e => feval e ct | None => None end.
Definition s5 := match s4 with Some e => feval e ct | None => None end.
Eval compute in s0.
Eval compute in s1.
Eval compute in s2.
Eval compute in s3.
Eval compute in s4.
Eval compute in s5.

Eval compute in teval myexp3 ct 100.

Definition myexp4 : exp := e_field (e_new Pair ((e_new C nil)::(e_field (e_new Pair ((e_new D nil)::(e_new C nil)::nil)) myFst)::nil) ) mySnd.

(* TODO: example of a single step using an evaluation context. prove example

Definition myexp5 : exp := 
Theorem rc_field_ex:
  eval myexp4

*)
**)