Require Import Atom.
Require Import FJ_Definitions.
Require Import FEV_Definitions.
Require Import List.

Definition C : atom := 2.
Definition D : atom := 3.
Definition Pair2 : atom := 4.
Definition mySetFst : atom := 5.
Definition myNewFst : atom := 6.
Definition myFst : atom := 7.
Definition mySnd : atom := 8.
Definition ct : ctable := ((C,(Object,nil,nil))
  ::(D,(Object,nil,nil))
  ::(Pair2,(Object,((myFst, Object) :: (mySnd, Object) :: nil),( (mySetFst,
         (Pair2, (myNewFst, Object) :: nil, e_new Pair2 (e_var myNewFst :: e_field (e_var this) mySnd :: nil)))
         :: nil ))) :: nil).
Definition myexp : exp := (e_field (e_new Pair2 ((e_new C nil)::(e_new D nil)::nil)) mySnd).
Definition myexp2 : exp := (e_meth (e_new Pair2 ((e_new C nil)::(e_new D nil)::nil)) mySetFst ((e_new C nil)::nil)).
Eval compute in feval myexp ct.
Eval compute in feval myexp2 ct.
Eval compute in match feval myexp2 ct with | Some (e_new c (H1::H2::T)) => feval H2 ct | _ => None end.
Definition myexp3 : exp := (e_field (e_field (e_new Pair2 ((e_new Pair2 ((e_new C nil)::(e_new D nil)::nil))::(e_new C nil)::nil)) myFst) mySnd).
Eval compute in feval myexp3 ct.
Eval compute in match feval myexp3 ct with | Some e => feval e ct | None => None end.
