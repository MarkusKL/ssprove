(* Definitions and proofs adapted from: https://github.com/alejandroag/analysis/blob/giry-impl/theories/giry.v *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets.
From mathcomp Require Import fsbigop functions reals topology separation_axioms.
From mathcomp Require Import ereal sequences numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


Section mzero_subprobability.
Context d (T : measurableType d) (R : realType).

Let mzero_setT : (@mzero d T R setT <= 1)%E.
Proof. by rewrite /mzero/=. Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ (@mzero d T R) mzero_setT.

End mzero_subprobability.


Definition disc_display : measure_display.
Proof. by constructor. Qed.

Definition D (T : Type) := T.

HB.instance Definition _ (T : eqType) := gen_eqMixin (D T).
HB.instance Definition _ (T : choiceType) := gen_choiceMixin (D T).
HB.instance Definition _ (T : pointedType) := isPointed.Build (D T) point.

HB.instance Definition _ (T : pointedType)
  := @isMeasurable.Build disc_display
  (D T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Section disc_def.
Local Open Scope classical_set_scope.
Context (T : pointedType) (R : realType).

Definition disc : Type := subprobability (D T) R.

HB.instance Definition _ := gen_eqMixin disc.
HB.instance Definition _ := gen_choiceMixin disc.
HB.instance Definition _ := isPointed.Build disc mzero.

Definition disc_ev (mu : disc) (A : set T) := mu A.

HB.instance Definition _ :=
  @isMeasurable.Build disc_display disc discrete_measurable
  discrete_measurable0 discrete_measurableC discrete_measurableU.

End disc_def.
Arguments disc _%type _.
Arguments disc_ev {T R} mu A.

Lemma eq_disc {T : pointedType} {R} (m1 m2 : disc T R)
  : m1 =1 m2 :> (set T -> \bar R) -> m1 = m2.
Proof.
  move: m1 m2 => [m1 +] [m2 +] /= m1m2.
  move/funext : m1m2 => <- -[[c11 c12] [m01] [sf1] [sig1] [fin1] [sub1]]
                      [[c21 c22] [m02] [sf2] [sig2] [fin2] [sub2]].
  have ? : c11 = c21 by []; subst c21.
  have ? : c12 = c22 by []; subst c22.
  have ? : m01 = m02 by []; subst m02.
  have ? : sf1 = sf2 by []; subst sf2.
  have ? : sig1 = sig2 by []; subst sig2.
  have ? : fin1 = fin2 by []; subst fin2.
  have ? : sub1 = sub2 by []; subst sub2.
  by f_equal.
Qed.


Section disc_ret.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context {T : pointedType} {R : realType}.

Definition disc_ret (x : T) : disc T R := \d_(x : D T).

End disc_ret.


Section disc_bind.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context (T1 : pointedType) (T2 : pointedType) (R : realType).
Variable (mu : disc T1 R) (f : T1 -> disc T2 R).

Let bind A := \int[mu]_x f x A.

Let bind0 : bind set0 = 0.
Proof. rewrite /bind integral0_eq //. Qed.

Let bind_ge0 A : 0 <= bind A.
Proof. rewrite /bind integral_ge0 //. Qed.

Let bind_semi_sigma_additive : semi_sigma_additive bind.
Proof.
move=> F mF tF _.
rewrite [X in _ --> X](_ : _ =
    (\int[mu]_x \sum_(0 <= k <oo) f x (F k))); last first.
  apply: eq_integral => mu' _.
  by apply/esym/cvg_lim => //; exact: measure_sigma_additive.
rewrite [X in X @ _](_ : _ =
    (fun n => (\int[mu]_x \sum_(0 <= i < n) f x (F i)))); last first.
  apply/funext => n; rewrite -ge0_integral_sum//.
apply: cvg_monotone_convergence => //.
- by move=> n x _; rewrite sume_ge0.
- by move=> x _ m n mn; exact: ereal_nondecreasing_series.
Qed.

HB.instance Definition _ := isMeasure.Build disc_display _ R bind
  bind0 bind_ge0 bind_semi_sigma_additive.

Let bind_setT : bind [set: T2] <= 1.
Proof.
rewrite (@le_trans _ _ (\int[mu]_x `|disc_ev (f x) [set: T2]|))//; last first.
  rewrite (le_trans _ (@sprobability_setT _ _ _ mu))//.
  rewrite -[leRHS]mul1e integral_le_bound//.
  by apply/aeW => x _; rewrite gee0_abs// sprobability_setT.
rewrite ge0_le_integral//=.
- by move=> x _; rewrite abse_ge0.
- by move=> x _; rewrite gee0_abs.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ bind bind_setT.

Definition disc_bind : disc T2 R := bind.

End disc_bind.
Arguments disc_bind {T1 T2 R}.


Section disc_lemmas.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context (T1 T2 T3 : pointedType) (R : realType).

Lemma disc_ret_bind (f : T1 -> disc T2 R) (x : T1)
  : disc_bind (disc_ret x) f = f x.
Proof.
  apply eq_disc => A /=.
  rewrite integral_dirac //.
  by rewrite diracE in_setT mul1e.
Qed.

Lemma disc_bind_ret (m : disc T1 R)
  : disc_bind m disc_ret = m.
Proof.
  apply eq_disc => A /=.
  rewrite -(mul1e (m A)).
  rewrite -integral_cst //.
  rewrite integral_mkcond.
  apply eq_integral => x H.
  rewrite diracE patchE.
  elim: (x \in A) => //.
Qed.

Import HBNNSimple.

Lemma sintegral_disc_bind (m : disc T1 R) (f : T1 -> disc T2 R)
  (h : {nnsfun D T2 >-> R}) :
  sintegral (disc_bind m f) h = \int[m]_x sintegral (f x) h.
Proof.
under eq_integral do rewrite sintegralE.
rewrite ge0_integral_fsum//; last 1 first.
  by move=> n x _; exact: nnsfun_mulemu_ge0.
rewrite sintegralE /=.
apply: fsbigop.eq_fsbigr => // r rh.
rewrite integralZl//.
have := finite_measure_integrable_cst m 1.
apply: le_integrable => //.
move=> x _ /=.
rewrite normr1 (le_trans _ (@sprobability_setT _ _ _ (f x)))// gee0_abs//.
by rewrite le_measure// ?inE.
Qed.

Lemma disc_bindE {m : disc T1 R} {f : T1 -> disc T2 R} {h : T2 -> \bar R} :
  (forall y, 0 <= h y) ->
  \int[disc_bind m f]_y h y = \int[m]_x \int[f x]_y h y.
Proof.
intros h0.
assert (mh : measurable_fun setT (h : D T2 -> \bar R)); [ done |].
pose g := nnsfun_approx measurableT mh.
pose gE := fun n => EFin \o g n.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n => \int[disc_bind m f]_y gE n y)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[m]_x \int[f x]_y gE n y)).
  apply: congr_lim; apply/funext => n.
  rewrite integralT_nnsfun sintegral_disc_bind; apply: eq_integral => x _.
  by rewrite integralT_nnsfun.
rewrite -monotone_convergence//; last 2 first.
  by move=> n x _; exact: integral_ge0.
  by move=> x _ n' n mn; apply: ge0_le_integral => // t _; exact: nd_gE.
apply: eq_integral => mu _.
rewrite -monotone_convergence//.
apply: eq_integral => t _.
by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.

Lemma disc_bind_assoc {m : disc T1 R} {f : T1 -> disc T2 R} {g : T2 -> disc T3 R}
  : disc_bind (disc_bind m f) g = disc_bind m (fun x => disc_bind (f x) g).
Proof.
  apply eq_disc => A /=.
  rewrite disc_bindE //.
Qed.

Lemma disc_interchange_measurable {mx my} {f : T1 * T2 -> disc T3 R} :
  (forall A, measurable_fun [set: D T1 * D T2] (f ^~ A)) ->
  disc_bind mx (fun x => disc_bind my (fun y => f (x, y)))
  = disc_bind my (fun y => disc_bind mx (fun x => f (x, y))).
Proof.
  intros H.
  apply eq_disc => A /=.
  rewrite (@fubini_tonelli _ _ _ _ _ mx my (f ^~ A)) //.
Qed.

Lemma disc_interchange_measurable_alt {mx my} {f : T1 -> T2 -> disc T3 R} :
  (forall A, measurable_fun [set: D T1 * D T2] (uncurry f ^~ A)) ->
  disc_bind mx (fun x => disc_bind my (fun y => f x y))
  = disc_bind my (fun y => disc_bind mx (fun x => f x y)).
Proof.
  intros.
  by apply (@disc_interchange_measurable mx my (uncurry f)).
Qed.

End disc_lemmas.

Definition disc_map {T1 T2 : pointedType} {R}
  (f : T1 -> T2) : disc T1 R -> disc T2 R
  := disc_bind ^~ (disc_ret \o f).

Lemma disc_map_ret {T1 T2 : pointedType} {R} (f : T1 -> T2) (x : T1)
  : disc_map f (disc_ret x) = @disc_ret _ R (f x).
Proof. rewrite /disc_map disc_ret_bind //. Qed.

Definition disc_fst {T1 T2 : pointedType} {R}
  : disc (T1 * T2) R -> disc T1 R
  := disc_map fst.

Definition disc_snd {T1 T2 : pointedType} {R}
  : disc (T1 * T2) R -> disc T2 R
  := disc_map snd.

Definition disc_pair {T1 T2 : pointedType} {R}
  : disc T1 R -> disc T2 R -> disc (T1 * T2) R
  := fun mx my => disc_bind mx (fun x => disc_map (pair x) my).

Lemma disc_fst_ret {T1 T2 : pointedType} {R} (x : T1) (y : T2) :
  disc_fst (disc_ret (x, y)) = @disc_ret _ R x.
Proof. rewrite /disc_fst disc_map_ret //. Qed.

Lemma disc_snd_ret {T1 T2 : pointedType} {R} (x : T1) (y : T2) :
  disc_snd (disc_ret (x, y)) = @disc_ret _ R y.
Proof. rewrite /disc_snd disc_map_ret //. Qed.

Lemma disc_fst_bind {T1 T1' T2 T2' : pointedType} {R}
  (m : disc (T1 * T2) R) (k : T1 * T2 -> disc (T1' * T2') R)
  (f : T1 -> disc T1' R) (y : T2)
  : (forall z, disc_fst (k z) = f (fst z))
  -> disc_fst (disc_bind m k)
   = disc_bind (disc_fst m) f.
Proof.
  intros H.
  rewrite /disc_fst /disc_map 2!disc_bind_assoc.
  f_equal; apply functional_extensionality_dep => xy /=.
  rewrite disc_ret_bind /=.
  apply H.
Qed.

Lemma disc_snd_bind {T1 T1' T2 T2' : pointedType} {R}
  (m : disc (T1 * T2) R) (k : T1 * T2 -> disc (T1' * T2') R)
  (g : T2 -> disc T2' R) (x : T1)
  : (forall z, disc_snd (k z) = g (snd z))
  -> disc_snd (disc_bind m k)
   = disc_bind (disc_snd m) g.
Proof.
  intros H.
  rewrite /disc_snd /disc_map 2!disc_bind_assoc.
  f_equal; apply functional_extensionality_dep => xy /=.
  rewrite disc_ret_bind /=.
  apply H.
Qed.


#[short(type=count1Type)]
HB.structure Definition Countable1 := {T of isPointed T & Countable T}.

HB.instance Definition _ {A B : count1Type} := Pointed.on (prod A B).

Section disc_lemma_countable.
Context {T1 T2 T3 : count1Type} {R : realType}.

Definition unprodD : D (T1 * T2) -> D T1 * D T2
  := fun a => a.

Definition prodD : (D T1 * D T2) -> D (T1 * T2)
  := fun a => a.

Lemma measurable_unprodD : measurable_fun setT unprodD.
Proof. done. Qed.

Lemma measurable_prodD : measurable_fun setT prodD.
Proof.
  intros S Y _.
  simpl in *.
  rewrite setTI /prodD preimage_id.
  replace Y with (\bigcup_(y : (T1 * T2)) if y \in Y then [set y] else set0)%classic.
  2: rewrite -bigcup_mkcond (bigcup_imset1 Y id) image_id //.
  apply countable_bigcupT_measurable.
  1: apply cardinality.countableP.
  intros [a b].
  destruct ((a, b) \in Y) => //.
  replace ([set (a, b)])%classic with ([set a] `*` [set b])%classic.
  2: apply eq_set => ab; destruct ab => //=. 
  2: apply boolp.propext.
  2: symmetry. 
  2: apply pair_equal_spec.
  by apply measurableX.
Qed.

Lemma disc_measurable_prod {d} {T : measurableType d} {f : D T1 * D T2 -> T}
  : measurable_fun setT f.
Proof.
  change f with (f \o unprodD \o prodD).
  apply (measurable_comp (F := setT)) => //.
  apply measurable_prodD.
Qed.

Lemma disc_interchange {mx my} {f : T1 -> T2 -> disc T3 R} :
  disc_bind mx (fun x => disc_bind my (fun y => f x y))
  = disc_bind my (fun y => disc_bind mx (fun x => f x y)).
Proof.
  rewrite disc_interchange_measurable_alt // => A.
  apply (disc_measurable_prod (f := uncurry f ^~ A)).
Qed.

End disc_lemma_countable.
