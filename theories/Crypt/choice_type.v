(**
  This file defines an inductive type [choice_type] corresponding to codes for
  choice types.
  We give a total order on this type, which is then used to show that
  [choice_type] forms a [choiceType].
 *)


From Coq Require Import Utf8.

(* !!! Import before mathcomp, to avoid overriding instances !!! *)
(* specifically, importing after mathcomp results in conflicting instances for
   Z_choiceType. *)
From deriving Require Import deriving.

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra word_ssrZ word.
(*From mathcomp Require Import word_ssrZ word.*)
(* From Jasmin Require Import utils word. *)
From SSProve.Crypt Require Import jasmin_word jasmin_util.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From HB Require Import structures.

From SSProve.Crypt Require Import Prelude Axioms Casts.
From extructures Require Import ord fset fmap.
Require Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Equations With UIP.



Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Open Scope fset.
Open Scope fset_scope.
Open Scope type_scope.


HB.mixin Record Initial A := {
  initial : A
}.

#[short(type="count1Type")]
HB.structure Definition Countable1 :=
  { A of Countable A & hasOrd A & Initial A }.

#[short(type="fin1Type")]
HB.structure Definition Finite1 :=
  { A of Finite A & hasOrd A & Initial A }.

Notation choice_type := count1Type.
Notation chUnit := (unit : choice_type).
Notation chNat := (nat : choice_type).
Notation chInt := (BinInt.Z : choice_type).
Notation chBool := (bool : choice_type).
Notation chProd a b := (prod a b : choice_type).
Notation chMap a b:= (FMap.FMap a b : choice_type).
Notation chOption a := (option a : choice_type).
Notation chFin n := (n : choice_type).
Notation chWord nbits := (word nbits : choice_type).
Notation chList := (list : choice_type).
Notation chSum := (sum : choice_type).

Derive NoConfusion NoConfusionHom for choice_type.

HB.instance Definition _ :=
  Initial.Build unit tt.

HB.instance Definition _ :=
  Initial.Build bool false.

HB.instance Definition _ :=
  Initial.Build nat 0.

HB.instance Definition _ :=
  Initial.Build int 0.

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

(* Gives universe inconsistencies
HB.instance Definition _ (n : nat) :=
  Initial.Build (ordinal (succn n)) Zp0.
 *)

Definition chElement_ordType (U : choice_type) : ordType := U.
Definition chElement (U : choice_type) : choiceType := U.

Coercion chElement : choice_type >-> choiceType.

Definition chCanonical (T : choice_type) := @initial T.

Definition cucumber {T : choice_type} := @pickle T.
Definition uncucumber {T : choice_type} := @unpickle T.
Lemma cucumberK U : pcancel (@cucumber U) uncucumber.
Proof. apply pickleK. Qed.

(*
Section Cucumber.
  (* Cucumber is a replacement for pickle until a
     countType for each choice_type can be given directly
     or until the inductive choice_type is removed entirely.
     The functions cucumber and uncucumber correspond to pickle
     and unpickle respectively.
   *)

  #[program] Fixpoint cucumber' {U : choice_type} : chElement_ordType U → nat :=
    match U with
    | chUnit => pickle
    | chNat => pickle
    | chInt => pickle
    | chBool => pickle
    | chProd _ _ => λ '(x, y), pickle (cucumber' x, cucumber' y)
    | chMap _ _ =>
        λ x, pickle (map (λ '(x, y), (cucumber' x, cucumber' y)) (\val x))
    | chOption _ => λ x, pickle (omap cucumber' x)
    | chFin _ => pickle
    | chWord _ => pickle
    | chList _ => λ x, pickle (map cucumber' x)
    | chSum _ _ => λ x,
      match x with
      | inl y => pickle (true, cucumber' y)
      | inr y => pickle (false, cucumber' y)
      end
    end.

  #[program] Fixpoint cucumber {U : choice_type} : U → nat :=
    match U with
    | chUnit => pickle
    | chNat => pickle
    | chInt => pickle
    | chBool => pickle
    | chProd _ _ => λ '(x, y), pickle (cucumber x, cucumber y)
    | chMap _ _ =>
        λ x, pickle (map (λ '(x, y), (cucumber' x, cucumber y)) (\val x))
    | chOption _ => λ x, pickle (omap cucumber x)
    | chFin _ => pickle
    | chWord _ => pickle
    | chList _ => λ x, pickle (map cucumber x)
    | chSum _ _ => λ x,
      match x with
      | inl y => pickle (true, cucumber y)
      | inr y => pickle (false, cucumber y)
      end
    end.

  Definition helper {U : countType} (x : U) : nat → U
    := λ n, locked (odflt x (unpickle n)).

  Lemma helperK U x : cancel (@pickle U) (helper x).
  Proof.
    intros y.
    rewrite /helper -lock pickleK //=.
  Qed.


  #[program] Fixpoint uncucumber'' {U : choice_type}
    : nat → chElement_ordType U :=
    match U with
    | chUnit => λ x, helper tt x
    | chNat => λ x, helper 0 x
    | chInt => λ x, helper BinInt.Z0 x
    | chBool => λ x, helper false x
    | chProd _ _ => λ x,
        let (y, z) := helper (0,0) x in (uncucumber'' y, uncucumber'' z)
    | chMap _ _ =>
        λ x, mkfmap (map (λ '(x, y), (uncucumber'' x, uncucumber'' y))
          (helper [::] x))
    | chOption _ =>
        λ x, omap uncucumber'' (helper None x)
    | chFin n => λ x, helper (Ordinal n.(cond_pos)) x
    | chWord _ => λ x, helper word0 x
    | chList _ => λ x,
        map uncucumber'' (helper [::] x)
    | chSum _ _ => λ x,
        let (b, n) := helper (true,0) x in
        if b then inl (uncucumber'' n) else inr (uncucumber'' n)
    end.

  #[program] Fixpoint uncucumber' {U : choice_type} : nat → U :=
    match U with
    | chUnit => λ x, helper tt x
    | chNat => λ x, helper 0 x
    | chInt => λ x, helper BinInt.Z0 x
    | chBool => λ x, helper false x
    | chProd _ _ => λ x,
        let (y, z) := helper (0,0) x in (uncucumber' y, uncucumber' z)
    | chMap _ _ =>
        λ x, mkfmap (map (λ '(x, y), (uncucumber'' x, uncucumber' y))
          (helper [::] x))
    | chOption _ =>
        λ x, omap uncucumber' (helper None x)
    | chFin n => λ x, helper (Ordinal n.(cond_pos)) x
    | chWord _ => λ x, helper word0 x
    | chList _ => λ x,
        map uncucumber' (helper [::] x)
    | chSum _ _ => λ x,
        let (b, n) := helper (true,0) x in
        if b then inl (uncucumber' n) else inr (uncucumber' n)
    end.

  Definition uncucumber {U : choice_type} : nat → option U :=
    λ n, locked (Some (uncucumber' n)).

  Lemma cucumber''K (U : choice_type) : cancel (@cucumber' U) uncucumber''.
  Proof.
    induction U => //=.
    all: intros x.
    all: try rewrite helperK //.
    + destruct x => //=.
      rewrite helperK IHU1 IHU2 //.
    + rewrite -map_comp //=.
      rewrite (@map_ext _ _ _ id).
      2: intros [a b] _; simpl.
      2: rewrite IHU1 IHU2 //.
      rewrite map_id.
      apply fmvalK.
    + apply omapK, IHU.
    + rewrite -map_comp.
      rewrite (@map_ext _ _ _ id).
      2: intros a _; rewrite //= IHU //.
      by rewrite map_id.
    + destruct x; rewrite helperK ?IHU1 ?IHU2 //.
  Qed.

  Lemma cucumber'K (U : choice_type) : cancel (@cucumber U) uncucumber'.
  Proof.
    induction U => //=.
    all: intros x.
    all: try rewrite helperK //.
    + destruct x => //=.
      rewrite helperK IHU1 IHU2 //.
    + rewrite -map_comp //=.
      rewrite (@map_ext _ _ _ id).
      2: intros [a b] _; simpl.
      2: rewrite cucumber''K IHU2 //.
      rewrite map_id.
      apply fmvalK.
    + apply omapK, IHU.
    + rewrite -map_comp.
      rewrite (@map_ext _ _ _ id).
      2: intros a _; rewrite //= IHU //.
      by rewrite map_id.
    + destruct x; rewrite helperK ?IHU1 ?IHU2 //.
  Qed.

  Lemma cucumberK U : pcancel (@cucumber U) uncucumber.
  Proof. intros x. rewrite /uncucumber -lock. f_equal. apply cucumber'K. Qed.

End Cucumber.
 *)


Definition coerce {A B : choice_type} : A → B
  := λ x, odflt (chCanonical B) (uncucumber (cucumber x)).

Lemma coerceE {A : choice_type} (a : A) : coerce a = a.
Proof. rewrite /coerce cucumberK //. Qed.
