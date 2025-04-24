(**
  This file defines an inductive type [choice_type] corresponding to codes for
  choice types.
  We give a total order on this type, which is then used to show that
  [choice_type] forms a [choiceType].
 *)


From Coq Require Import Utf8 Lia.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples GenericRulesSimple.

(* !!! Import before mathcomp, to avoid overriding instances !!! *)
(* specifically, importing after mathcomp results in conflicting instances for
   Z_choiceType. *)
From deriving Require Import deriving.

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr realsum seq all_algebra fintype.
From mathcomp Require Import word_ssrZ word.
(* From Jasmin Require Import utils word. *)
From SSProve.Crypt Require Import jasmin_word jasmin_util.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.

From SSProve.Crypt Require Import Prelude Axioms Casts.
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.

Import SPropNotations.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.

(*
HB.mixin Record Inhabited A := {
  canonical : A;
}.

#[short(type="choice_type")]
HB.structure Definition LocationType := { A of Countable A & Inhabited A }.
 *)

About unit.
Lemma can_unit : cancel (λ tt, true) (λ _, tt).
Proof. by intros []. Qed.

HB.instance Definition _ := CanIsCountable can_unit.
HB.instance Definition _ := CanIsFinite can_unit.

HB.mixin Record Initial A := {
  initial : A
}.

(*
#[short(type="initType")]
HB.structure Definition Init := { A of Initial A }.
 *)

#[short(type="count1Type")]
HB.structure Definition Countable1 := { A of Countable A & Initial A }.

#[short(type="fin1Type")]
HB.structure Definition Finite1 := { A of Finite A & Initial A }.

(* groups as fin1Type?
HB.builders Context A (a : GRing.isNmodule A).

  HB.instance Definition _ :=
    Initial.Build A zero.

HB.end.
 *)

HB.instance Definition _ :=
  Initial.Build unit tt.

HB.instance Definition _ :=
  Initial.Build Datatypes.unit Datatypes.tt.

HB.instance Definition _ :=
  Initial.Build nat 0.

HB.instance Definition _ :=
  Initial.Build int 0.

HB.instance Definition _ :=
  Initial.Build bool false.

(* MK: In principle this could be a countType, however it gives universe inconsistencies later. *)
HB.instance Definition _ {T : count1Type} :=
  Initial.Build (option T) None.

HB.instance Definition _ {T : fin1Type} :=
  Initial.Build (option T) None.

HB.instance Definition _ {T : count1Type} {S : count1Type} :=
  Initial.Build (T + S) (inl initial).

HB.instance Definition _ {T : fin1Type} {S : fin1Type} :=
  Initial.Build (T + S) (inl initial).

HB.instance Definition _ {T S : count1Type} :=
  Initial.Build (T * S) (initial, initial).

HB.instance Definition _ {T S : fin1Type} :=
  Initial.Build (T * S) (initial, initial).

HB.instance Definition _ {T : count1Type} :=
  Initial.Build (seq T) [::].

HB.instance Definition _ {T : count1Type} :=
  Initial.Build (seq T) [::].

(*
Search "HasOrd" ordType.
HB.builders Context A (a : Countable A).

  HB.instance Definition _ :=
    @PcanHasOrd A nat (λ x, pickle x) unpickle pickleK.

HB.end.
 *)


  (*
HB.instance Definition _ {T : ordType} :=
  @CanIsCountable (seq T) {fset T} _ _ ((@fsvalK _)).
   *)


(*
HB.instance Definition _ {T : ordType} :=
  Initial.Build {fset T} fset0.
 *)


Definition canonical {S : count1Type} : S := initial.
Definition choice_type := count1Type.

(* backwards compatibility *)
(* Notation choice_type := Type. *)

(*
HB.instance Definition _ := CanIsCountable natsum_of_intK.
 *)
