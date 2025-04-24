(** Heaps for code/packages

  This module introduces the notion of heap for storing memory in packages.
*)


From Coq Require Import Utf8.
Require Import ZArith.
From SSProve.Relational Require Import OrderEnrichedCategory
  OrderEnrichedRelativeMonadExamples.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve.Mon Require Import SPropBase.
From SSProve.Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
From mathcomp Require Import word.

(* Must come after importing Equations.Equations, who knows why. *)
From SSProve.Crypt Require Import FreeProbProg.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Definition heap := {fmap nat -> nat}.
(* Check (heap : choiceType). *)

(*
Definition check_loc_val (l : Location) (v : nat) :=
  l.2 == v.π1.

Definition valid_location (h : raw_heap) (l : Location) :=
  match h l with
  | None => false
  | Some v => check_loc_val l v
  end.

Definition valid_heap : pred raw_heap :=
  λ h, domm h == fset_filter (valid_location h) (domm h).

Definition heap_defaults := ∀ a : choice_type, a.

Definition heap_init : heap_defaults.
Proof.
  intros a. induction a.
  - exact tt.
  - exact 0.
  - exact Z0.
  - exact false.
  - exact (IHa1, IHa2).
  - exact emptym.
  - exact None.
  - exact (fintype.Ordinal n.(cond_pos)).
  - exact word0.
  - exact [::].
  - exact (inl IHa1).
Defined.

Definition heap := { h : raw_heap | valid_heap h }.

Definition heap_choiceType := Choice.clone _ heap.

Lemma heap_ext :
  ∀ (h₀ h₁ : heap),
    h₀ ∙1 = h₁ ∙1 →
    h₀ = h₁.
Proof.
  intros [h₀ v₀] [h₁ v₁] e. simpl in e. subst.
  f_equal. apply eq_irrelevance.
Qed.
 *)

(*
Definition cast_pointed_value {A} (p : pointed_value) (e : A = p.π1) : Value A.
Proof.
  subst. exact p.π2.
Defined.

Lemma cast_pointed_value_K :
  ∀ p e,
    cast_pointed_value p e = p.π2.
Proof.
  intros p e.
  assert (e = erefl).
  { apply eq_irrelevance. }
  subst. reflexivity.
Qed.

Lemma cast_pointed_value_ext :
  ∀ A p e1 q e2,
    p = q →
    @cast_pointed_value A p e1 = @cast_pointed_value A q e2.
Proof.
  intros A p e1 q e2 e. subst.
  cbn.
  assert (ee : e2 = erefl).
  { apply eq_irrelevance. }
  rewrite ee. reflexivity.
Qed.

Lemma get_heap_helper :
  ∀ h ℓ p,
    valid_heap h →
    h ℓ = Some p →
    ℓ.2 = p.π1.
Proof.
  intros h ℓ p vh e.
  assert (hℓ : exists v, h ℓ = Some v).
  { eexists. eauto. }
  move: hℓ => /dommP hℓ.
  unfold valid_heap in vh.
  move: vh => /eqP vh.
  rewrite vh in hℓ.
  rewrite in_fset_filter in hℓ.
  move: hℓ => /andP [vℓ hℓ].
  unfold valid_location in vℓ.
  rewrite e in vℓ.
  unfold check_loc_val in vℓ.
  move: vℓ => /eqP. auto.
Qed.
 *)

Definition get_heap (map : heap) (l : Location) : l :=
  odflt initial (obind unpickle (map l.1)).

Definition set_heap (map : heap) (l : Location) (v : l) : heap :=
  setm map l.1 (pickle v).

(*
Equations? get_heap (map : heap) (ℓ : Location) : Value ℓ :=
  get_heap map ℓ with inspect (map ∙1 ℓ) := {
  | @exist (Some p) e => cast_pointed_value p _
  | @exist None e => heap_init ℓ
  }.
Proof.
  destruct map as [h vh]. simpl in e.
  eapply get_heap_helper. all: eauto.
Defined.
 *)


(*
Program Definition set_heap (map : heap) (l : Location) (v : Value l)
: heap :=
  setm map l (l ; v).
Next Obligation.
  intros map l v.
  unfold valid_heap.
  destruct map as [rh valid_rh].
  cbn - ["_ == _"].
  apply /eqP.
  apply eq_fset.
  move => x.
  rewrite domm_set.
  rewrite in_fset_filter.
  destruct ((x \in l |: domm rh)) eqn:Heq.
  - rewrite andbC. cbn.
    symmetry. apply /idP.
    unfold valid_location.
    rewrite setmE.
    destruct (x == l) eqn:H.
    + cbn. move: H. move /eqP => H. subst. apply choice_type_refl.
    + move: Heq. move /idP /fsetU1P => Heq.
      destruct Heq.
      * move: H. move /eqP => H. contradiction.
      * destruct x, l. rewrite mem_domm in H0.
        unfold isSome in H0.
        destruct (rh (s, s0)) eqn:Hrhx.
        ** cbn. unfold valid_heap in valid_rh.
            move: valid_rh. move /eqP /eq_fset => valid_rh.
            specialize (valid_rh (s, s0)).
            rewrite in_fset_filter in valid_rh.
            rewrite mem_domm in valid_rh.
            assert (valid_location rh (s, s0)) as Hvl.
            { rewrite Hrhx in valid_rh. cbn in valid_rh.
              rewrite andbC in valid_rh. cbn in valid_rh.
              rewrite -valid_rh. auto. }
            unfold valid_location in Hvl.
            rewrite Hrhx in Hvl.
            cbn in Hvl.
            assumption.
        ** assumption.
  - rewrite andbC. auto.
Qed.
 *)

Definition empty_heap : heap := emptym.

Lemma get_empty_heap :
  ∀ ℓ,
    get_heap empty_heap ℓ = initial.
Proof.
  intros ℓ. reflexivity.
Qed.

Lemma get_set_heap_eq :
  ∀ h ℓ v,
    get_heap (set_heap h ℓ v) ℓ = v.
Proof.
  intros h l v.
  unfold set_heap, get_heap.
  rewrite setmE eq_refl //= pickleK //.
Qed.

Lemma get_set_heap_neq :
  ∀ h ℓ v ℓ',
    ℓ'.1 != ℓ.1 →
    get_heap (set_heap h ℓ v) ℓ' = get_heap h ℓ'.
Proof.
  move=> h l v l' /negPf H.
  unfold set_heap, get_heap.
  rewrite setmE H //.
Qed.

Lemma set_heap_contract :
  ∀ s ℓ v v',
    set_heap (set_heap s ℓ v) ℓ v' = set_heap s ℓ v'.
Proof.
  intros s l v v'.
  unfold set_heap, get_heap.
  rewrite setmxx //.
Qed.

(* MK: remove? symmtric of get_set_heap_neq *)
Lemma get_heap_set_heap :
  ∀ s ℓ ℓ' v,
    ℓ.1 != ℓ'.1 →
    get_heap s ℓ = get_heap (set_heap s ℓ' v) ℓ.
Proof.
  move=> s l l' v H.
  rewrite get_set_heap_neq //.
Qed.

Lemma set_heap_commut :
  ∀ s ℓ v ℓ' v',
    ℓ.1 != ℓ'.1 →
    set_heap (set_heap s ℓ v) ℓ' v' =
    set_heap (set_heap s ℓ' v') ℓ v.
Proof.
  intros s l v l' v' H.
  unfold set_heap, get_heap.
  rewrite setmC //.
Qed.
