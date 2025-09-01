(* File origin: https://github.com/alejandroag/analysis/blob/giry-impl/theories/giry.v *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp classical_sets.
From mathcomp Require Import fsbigop functions reals topology separation_axioms.
From mathcomp Require Import ereal sequences numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.


(* TODO: PR to measure.v? *)
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

(*
Lemma giry_int_ret (x : T) (f : T -> \bar R) : measurable_fun [set: T] f ->
  giry_int (giry_ret x) f = f x.
Proof.
by move=> mf; rewrite /giry_int /giry_ret integral_dirac// diracT mul1e.
Qed.
 *)

End disc_ret.


Section disc_bind.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Context (T1 : pointedType) (T2 : pointedType) (R : realType).
Variable (mu : disc T1 R) (f : T1 -> disc T2 R).

Let bind A := \int[mu]_x f x A.

Let bind0 : bind set0 = 0.
Proof. Admitted.

Let bind_ge0 A : 0 <= bind A. Proof. Admitted.

Let bind_semi_sigma_additive : semi_sigma_additive bind.
Proof. Admitted.

HB.instance Definition _ := isMeasure.Build disc_display _ R bind
  bind0 bind_ge0 bind_semi_sigma_additive.

Let bind_setT : bind [set: T2] <= 1.
Proof. Admitted.

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

Definition disc_fst {T1 T2 : pointedType} {R}
  : disc (T1 * T2)%type R -> disc T1 R
  := disc_map fst.

Definition disc_snd {T1 T2 : pointedType} {R}
  : disc (T1 * T2)%type R -> disc T2 R
  := disc_map snd.

Definition disc_pair {T1 T2 : pointedType} {R}
  : disc T1 R -> disc T2 R -> disc (T1 * T2)%type R
  := fun mx my => disc_bind mx (fun x => disc_map (pair x) my).

(*
Lemma disc_bind_cst {T1 T2 : pointedType} {R} 
  (mx : disc T1 R) (my : disc T2 R) :
  disc_bind mx (fun=> my) = my.
Proof.
  apply eq_disc => A.
  simpl.
  rewrite disc_bindE.
 *)

Lemma dirac_pair {T1 T2 : pointedType} {R} (x : T1) (y : T2) A :
  @dirac _ (D (T1 * T2)) (x, y) R A
  = (dirac (x : D T1) (ysection A y) * dirac (y : D T2) (xsection A x))%E.
Proof.
  rewrite 3!diracE.
  rewrite mem_xsection mem_ysection.
  rewrite -EFinM -natrM mulnb.
  rewrite Bool.andb_diag //.
Qed.

Lemma disc_ret_pair {T1 T2 : pointedType} {R} (x : T1) (y : T2) A :
  @disc_ret _ R (x, y) A =
    (disc_ret x (ysection A y) * disc_ret y (xsection A x))%E.
Proof.
  rewrite /disc_ret /= 3!diracE.
  rewrite mem_xsection mem_ysection.
  rewrite -EFinM -natrM mulnb.
  rewrite Bool.andb_diag //.
Qed.

#[short(type=count1Type)]
HB.structure Definition Countable1 := {T of isPointed T & Countable T}.

HB.instance Definition _ {A B : count1Type} := Pointed.on (prod A B).

Lemma eq_pointwise {T : count1Type} {R} (m1 m2 : disc T R)
  : m1 \o set1 =1 m2 \o set1 :> (T -> \bar R) -> m1 = m2.
Proof.
  intros H.
  apply eq_disc => A.
  replace A with (\bigcup_(x in A) [set x])%classic.
  2: rewrite bigcup_imset1 image_id //.
  Search (\bigcup_(_ in _) _)%classic.
Admitted.

Section disc_lemma_countable.
Context {T1 T2 : count1Type} {R : realType}.

Lemma disc_test (x : T1) (y : T2) d :
  disc_fst d = disc_ret x ->
  disc_snd d = disc_ret y ->
  d = @disc_ret _ R (x, y).
Proof.
  intros H H'.
  apply eq_disc => A /=.
  rewrite disc_ret_pair -{}H -{}H'.
  unfold disc_fst, disc_snd, disc_map.
  Search (_ * _)%E.

  
  rewrite disc_
  do 2 rewrite integral_indic //=.
  rewrite 2!setIT.
  Search (_ * _)%E.
  Search product_measure1.
  rewrite -product_measure1E //.
  Search (_ * _)%E.


  apply @eq_pointwise => xy.
  (*apply eq_disc => A /=.*)
  simpl.
  rewrite disc_ret_pair -{}H -{}H' /=.
  destruct xy as [x' y'].
  under eq_integral.
  intros.
  rewrite (@ysection_indic R) => /=.
  unfold dirac. simpl.
  over.
  simpl.
  Search indic integral.
  rewrite integral_indic //.
  rewrite integral_indic //.
  Search (\
  Search indic.
  rewrite indicE.

  unfold dirac.
  Search dirac.
  rewrite dirac_indic.
  rewrite ysectionE /= preimage1.
  rewrite ysection1.
  rewrite ysection_indic.

  Search (_ * _)%E integral.
  rewrite integralZl.

  under eq_integral.
  intros. rewrite diracE.
  rewrite mem_ysection. over.
  simpl.
  Search (\int[_]__ _)%E.
  Check counting.

  unfold disc_fst, disc_snd.
  unfold disc_map.
  simpl.
  rewrite diracE.
  Search ysection.
  Search xsection.
  Search (_ * _)%E.
  Search integral (_ * _)%E.
  rewrite -H.
  eapply (f_equal disc_ev) in H.
  unfold disc_ev in H => //.
  Search (_ = _ :> _ -> _).
  eapply 
  rewrite H.
  simpl in H.

  rewrite -H.
  simpl in H.
  rewrite /= diracE.
  Search ((_, _) \in _).



Lemma disc_pair_ret {T1 T2 : pointedType} {R} {x : T1} {y : T2}
  : disc_pair (disc_ret x) (disc_ret y) = @disc_ret _ R (x, y).
Proof. rewrite /disc_pair /disc_map 2!disc_ret_bind //. Qed.

Lemma disc_pair_fst_snd {T1 T2 : pointedType} {R} {m : disc (T1 * T2)%type R}
  : disc_pair (disc_fst m) (disc_snd m) = m.
Proof.
  unfold disc_pair.
  unfold disc_fst, disc_snd.
  unfold disc_map.
  rewrite disc_bind_assoc /=.
  rewrite disc_ret_bind.

  simpl.
rewrite /disc_pair /disc_map 2!disc_ret_bind //. Qed.


Lemma disc_snd_pair {T1 T2 : pointedType} {R}
  (mx : disc T1 R) (my : disc T2 R)
  : disc_snd (disc_pair mx my) = disc_bind mx (fun=> my).
Proof.
  unfold disc_snd, disc_pair, disc_map.
  rewrite disc_bind_assoc.
  f_equal; apply functional_extensionality_dep => x.
  rewrite -{2}(disc_bind_ret my).
  rewrite disc_bind_assoc.
  f_equal; apply functional_extensionality_dep => y.
  rewrite disc_ret_bind //.
Qed.

Lemma disc_fst_pair {T1 T2 : pointedType} {R}
  (mx : disc T1 R) (my : disc T2 R)
  : disc_fst (disc_pair mx my) = disc_bind mx (fun x => disc_map (cst x) my).
Proof.
  unfold disc_fst, disc_pair, disc_map.
  replace mx with (disc_bind mx disc_ret); [| by rewrite disc_bind_ret ].
  etransitivity.
  2: apply (@disc_interchange_measurable_alt _ _ _ _ mx my (fun x y => disc_ret x)).
  2: move=> A /=.

  rewrite -{2}(disc_bind_ret mx).
  f_equal; apply functional_extensionality_dep => x.
  rewrite disc_bind_assoc /=.
  transitivity (disc_bind my (fun y => disc_ret (x, y).1)).
  f_equal; apply functional_extensionality_dep => y.
  rewrite disc_ret_bind //.
  simpl.
  rewrite disc_bind_ret.
  Search disc_ret.
  transitivity (disc_bind mx disc_ret).
    f_equal.
    Search "exten".
  Check disc_bind_ret.
  apply eq_disc => A.
  apply eq_disc => A /=.
  unfold disc_fst, disc_pair, disc_map.

  rewrite disc_bind_assoc.

Local Notation "m >>= mf" := (giry_bind m mf).

Lemma measurable_giry_bind f (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: giry T1 R] (fun mu => mu >>= mf).
Proof.
apply: (@measurableT_comp _ _ _ _ _ _ _ _ (giry_map mf)) => //=.
  exact: measurable_giry_join.
exact: measurable_giry_map.
Qed.

Lemma giry_int_bind mu f (mf : measurable_fun [set: T1] f) (h : T2 -> \bar R) :
    measurable_fun [set: T2] h -> (forall x, 0 <= h x)%E ->
  giry_int (mu >>= mf) h = giry_int mu (fun x => giry_int (f x) h).
Proof.
move=> mh h0; rewrite /giry_bind /= giry_int_join// giry_int_map//.
  exact: measurable_giry_int.
by move=> ?; exact: integral_ge0.
Qed.

End giry_bind.



Section giry_integral.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).

Definition giry_int (mu : giry T R) (f : T -> \bar R) := \int[mu]_x f x.

Import HBNNSimple.

Lemma measurable_giry_int (f : T -> \bar R) :
  measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  measurable_fun [set: giry T R] (giry_int ^~ f).
Proof.
(*
  The idea is to reconstruct f from simple functions, then use measurability of giry_ev.
  Tom Avery. Codensity and the Giry monad. https://arxiv.org/pdf/1410.4432.
 *)
move=> mf h0.
pose g := nnsfun_approx measurableT mf.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (gE n) by exact/measurable_EFinP.
have gE0 n x : [set: T] x -> 0 <= (gE n) x by rewrite /gE /= // lee_fin.
have HgEmono x : [set: T] x -> {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> _ n m nm; exact/lefP/nd_nnsfun_approx.
(* By MCT, limit of the integrals of g_n is the integral of the limit of g_n *)
have Hcvg := cvg_monotone_convergence _ mgE gE0 HgEmono.
pose gEInt := fun n μ => \int[μ]_x (gE n) x.
have mgEInt n : measurable_fun [set: giry T R] (gEInt n).
  rewrite /gEInt /gE /=.
  apply (eq_measurable_fun (fun μ : giry T R =>
    \sum_(x \in range (g n)) x%:E * μ (g n @^-1` [set x]))).
    by move=> μ Hμ; rewrite integralT_nnsfun sintegralE.
  apply: emeasurable_fsum => // r.
  apply: measurable_funeM.
  exact: measurable_giry_ev.
(* The μ ↦ int[mu] lim g_n is measurable if every μ ↦ int[mu] g_n is measurable *)
apply: (emeasurable_fun_cvg _ (fun μ : giry T R => \int[μ]_x f x) mgEInt).
move=> μ Hμ.
rewrite /gEInt /=.
rewrite (eq_integral (fun x : T => limn (gE ^~ x))).
  exact: (Hcvg μ measurableT).
move=> x _; apply/esym/cvg_lim  => //.
exact/cvg_nnsfun_approx.
Qed.

End giry_integral.
Arguments giry_int {d T R} mu f.

Local Open Scope classical_set_scope.
(* Adapted from mathlib induction_on_inter *)
(* TODO: change premises to use setX_closed like notations *)
Lemma dynkin_induction d {T : measurableType d} (G : set (set T))
    (P : set_system T) :
  @measurable _ T = <<s G >> ->
  setI_closed G ->
  P [set: T] ->
  G `<=` P ->
  (forall S, measurable S -> P S -> P (~` S)) ->
  (forall F : (set T)^nat,
    (forall n, measurable (F n)) ->
    trivIset setT F ->
    (forall n, P (F n)) -> P (\bigcup_k F k)) ->
  (forall S, <<s G >> S -> P S).
Proof.
move=> GE GI PsetT GP PsetC Pbigcup A sGA.
suff: <<s G >> `<=` [set A | measurable A /\ P A] by move=> /(_ _ sGA)[].
apply: lambda_system_subset; [by []| | |by []].
- apply/dynkin_lambda_system; split => //.
  + by move=> B [mB PB]; split; [exact: measurableC|exact: PsetC].
  + move=> F tF Hm; split.
      by apply: bigcup_measurable => k _; apply Hm.
    by apply: Pbigcup => //; apply Hm.
- move=> B GB; split; last exact: GP.
  by rewrite GE; exact: sub_gen_smallest.
Qed.
Local Close Scope classical_set_scope.

Section measurable_giry_codensity.
Local Open Scope classical_set_scope.

(* TODO: move this lemma to a more accessible location? *)
Let measurability_image_sub d d' (aT : measurableType d) (rT : measurableType d')
    (f : aT -> rT) (G : set (set rT)) :
    @measurable _ rT = <<s G >> ->
    (forall B, G B -> measurable (f @^-1` B)) ->
  measurable_fun [set: aT] f.
Proof.
move=> GE Gf; apply/(measurability (G:=G)) => //.
by apply/image_subP => A /Gf; rewrite setTI.
Qed.

Lemma measurable_giry_codensity {d1} {d2} {T1 : measurableType d1}
    {T2 : measurableType d2} {R : realType} (f : T1 -> giry T2 R) :
  (forall B, measurable B -> measurable_fun [set: T1] (f ^~ B)) ->
  measurable_fun [set: T1] f.
Proof.
move=> mf.
pose G : set_system (giry T2 R) := \bigcup_(B in measurable) preimg_giry_ev B.
apply: (measurability_image_sub (G := G)) => // _ [B mB [Y mY] <-].
exact: mf.
Qed.

End measurable_giry_codensity.

Section giry_map.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.

Variables (f : T1 -> T2) (mf : measurable_fun [set: T1] f) (mu1 : giry T1 R).

Let map := pushforward mu1 mf.

Let map0 : map set0 = 0. Proof. exact: measure0. Qed.

Let map_ge0 A : 0 <= map A. Proof. exact: measure_ge0. Qed.

Let map_sigma_additive : semi_sigma_additive map.
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ map
  map0 map_ge0 map_sigma_additive.

(* used to work before the change of definition of pushforward
HB.instance Definition _ := Measure.on gMap_ev.
the change of definition was maybe not a good idea...
https://github.com/math-comp/analysis/pull/1661
*)

Let map_setT : map [set: T2] <= 1.
Proof. by rewrite /map /pushforward /= sprobability_setT. Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ map map_setT.

Definition giry_map : giry T2 R := map.

End giry_map.

Section giry_map_meas.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Implicit Type f : T1 -> T2.

Lemma giry_int_map f (mf : measurable_fun [set: T1] f)
    (mu : giry T1 R) (h : T2 -> \bar R) :
  measurable_fun [set: T2] h -> (forall x, 0 <= h x) ->
  giry_int (giry_map mf mu) h = giry_int mu (h \o f).
Proof. by move=> mh h0; exact: ge0_integral_pushforward. Qed.

Lemma giry_mapE f (mf : measurable_fun [set: T1] f)
    (mu1 : giry T1 R) (B : set T2) : measurable B ->
  giry_map mf mu1 B = \int[mu1]_x (\d_(f x))%R B.
Proof.
move=> mA.
rewrite -[in LHS](setIT B) -[LHS]integral_indic// [LHS]giry_int_map//.
  exact/measurable_EFinP/measurable_indic.
by move=> ?; rewrite lee_fin.
Qed.

Lemma measurable_giry_map f (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: giry T1 R] (giry_map mf).
Proof.
rewrite /giry_map.
apply: (@measurable_giry_codensity _ _ (giry T1 R)) => B mB.
apply: measurable_giry_ev.
by rewrite -(setTI (f @^-1` B)); exact: mf.
Qed.

End giry_map_meas.

Section giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable M : giry (giry T R) R.

Let join A := giry_int M (giry_ev ^~ A).

Let join0 : join set0 = 0.
Proof. by rewrite /join /giry_ev /giry_int/= integral0_eq. Qed.

Let join_ge0 A : 0 <= join A. Proof. by rewrite /join integral_ge0. Qed.

Let join_semi_sigma_additive : semi_sigma_additive join.
Proof.
move=> F mF tF _; rewrite [X in _ --> X](_ : _ =
    giry_int M (fun x => \sum_(0 <= k <oo) x (F k))); last first.
  apply: eq_integral => mu _.
  by apply/esym/cvg_lim => //; exact: measure_sigma_additive.
rewrite [X in X @ _](_ : _ =
    (fun n => giry_int M (fun mu => \sum_(0 <= i < n) mu (F i)))); last first.
  apply/funext => n; rewrite -ge0_integral_sum//.
  by move=> ?; exact: measurable_giry_ev.
apply: cvg_monotone_convergence => //.
- by move=> n; apply: emeasurable_sum => m; exact: measurable_giry_ev.
- by move=> n x _; rewrite sume_ge0.
- by move=> x _ m n mn; exact: ereal_nondecreasing_series.
Qed.

HB.instance Definition _ := isMeasure.Build d _ R join
  join0 join_ge0 join_semi_sigma_additive.

Let join_setT : join [set: T] <= 1.
Proof.
rewrite (@le_trans _ _ (\int[M]_x `|giry_ev x [set: T]|))//; last first.
  rewrite (le_trans _ (@sprobability_setT _ _ _ M))//.
  rewrite -[leRHS]mul1e integral_le_bound//.
    exact: measurable_giry_ev.
  by apply/aeW => x _; rewrite gee0_abs// sprobability_setT.
rewrite ge0_le_integral//=.
- exact: measurable_giry_ev.
- by move=> x _; rewrite abse_ge0.
- by apply: measurableT_comp => //; exact: measurable_giry_ev.
- by move=> x _; rewrite gee0_abs.
Qed.

HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ join join_setT.

Definition giry_join : giry T R := join.

End giry_join.
Arguments giry_join {d T R}.

Section measurable_giry_join.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d} {T : measurableType d} {R : realType}.

Lemma measurable_giry_join : measurable_fun [set: giry (giry T R) R] giry_join.
Proof.
apply: measurable_giry_codensity => B mB/=.
by apply: measurable_giry_int => //; exact: measurable_giry_ev.
Qed.

Import HBNNSimple.

Lemma sintegral_giry_join (M : giry (giry T R) R) (h : {nnsfun T >-> R}) :
  sintegral (giry_join M) h = \int[M]_mu sintegral mu h.
Proof.
under eq_integral do rewrite sintegralE.
rewrite ge0_integral_fsum//; last 2 first.
  by move=> r; apply: measurable_funeM; exact: measurable_giry_ev.
  by move=> n x _; exact: nnsfun_mulemu_ge0.
rewrite sintegralE /=.
apply: fsbigop.eq_fsbigr => // r rh.
rewrite integralZl//.
have := finite_measure_integrable_cst M 1.
apply: le_integrable => //; first exact: measurable_giry_ev.
move=> mu _ /=.
rewrite normr1 (le_trans _ (@sprobability_setT _ _ _ mu))// gee0_abs//.
by rewrite le_measure// ?inE.
Qed.

Lemma giry_int_join (M : giry (giry T R) R) (h : T -> \bar R) :
    measurable_fun [set: T] h -> (forall x, 0 <= h x) ->
  giry_int (giry_join M) h = giry_int M (giry_int ^~ h).
Proof.
move=> mh h0.
pose g := nnsfun_approx measurableT mh.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (gE n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n m / (n <= m)%O >-> n <= m}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
rewrite /giry_int.
transitivity (limn (fun n => \int[giry_join M]_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[M]_mu \int[mu]_x gE n x)).
  apply: congr_lim; apply/funext => n.
  rewrite integralT_nnsfun sintegral_giry_join; apply: eq_integral => x _.
  by rewrite integralT_nnsfun.
rewrite -monotone_convergence//; last 3 first.
  by move=> n; exact: measurable_giry_int.
  by move=> n x _; exact: integral_ge0.
  by move=> x _ m n mn; apply: ge0_le_integral => // t _; exact: nd_gE.
apply: eq_integral => mu _.
rewrite -monotone_convergence//.
apply: eq_integral => t _.
by apply/cvg_lim => //; exact: cvg_nnsfun_approx.
Qed.

End measurable_giry_join.

Reserved Notation "m >>= f" (at level 49).


Section giry_monad.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2)
  (T3 : measurableType d3) (R : realType).

Lemma giry_joinA (x : giry (giry (giry T1 R) R) R) :
  (giry_join \o giry_map measurable_giry_join) x ≡μ
  (giry_join \o giry_join) x.
Proof.
move=> A mA/=.
rewrite giry_int_map//; last exact: measurable_giry_ev.
by rewrite giry_int_join//; exact: measurable_giry_ev.
Qed.

Lemma giry_join_id1 (x : giry T1 R) :
  (giry_join \o giry_map measurable_giry_ret) x ≡μ
  (giry_join \o giry_ret) x.
Proof.
move=> A mA/=.
rewrite giry_int_map//; last exact: measurable_giry_ev.
rewrite giry_int_ret//; last exact: measurable_giry_ev.
by rewrite /giry_int /giry_ev /giry_ret/= /dirac integral_indic// setIT.
Qed.

Lemma giry_join_id2 (x : giry (giry T1 R) R) (f : T1 -> T2)
    (mf : measurable_fun [set: T1] f) :
  (giry_join \o giry_map (measurable_giry_map mf)) x ≡μ
  (giry_map mf \o giry_join) x.
Proof.
by move=> X mS /=; rewrite giry_int_map//; exact: measurable_giry_ev.
Qed.

End giry_monad.

Section giry_map_zero.
Local Open Scope classical_set_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

Lemma giry_map_zero (f : T1 -> T2) (mf : measurable_fun [set: T1] f) :
  giry_map mf (@mzero d1 T1 R) ≡μ @mzero d2 T2 R.
Proof. by []. Qed.

End giry_map_zero.

Section giry_prod.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} {R : realType}.
Variable μ12 : giry T1 R * giry T2 R.

(* https://en.wikipedia.org/wiki/Giry_monad#Product_distributions  *)
Let prod := μ12.1 \x μ12.2.

HB.instance Definition _ := Measure.on prod.

Let prod_setT : prod setT <= 1.
Proof.
rewrite -setXTT [leLHS]product_measure1E// -[leRHS]mule1.
by rewrite lee_pmul// sprobability_setT.
Qed.

HB.instance Definition _ :=
  Measure_isSubProbability.Build _ _ _ prod prod_setT.

Definition giry_prod : giry (T1 * T2)%type R := prod.

(*  gBind' (fun v1 => gBind' (gRet \o (pair v1)) (snd μ)) (fst μ). *)

End giry_prod.

Section measurable_giry_prod.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.

(* TODO: Clean up, maybe move elsewhere *)
Lemma subprobability_prod_setC (P : giry T1 R * giry T2 R) (A : set (T1 * T2)) :
  measurable A ->
  (P.1 \x P.2) (~` A) = (P.1 \x P.2) [set: T1 * T2] - (P.1 \x P.2) A.
Proof.
move=> mA; rewrite -(setvU A) measureU//= ?addeK ?setICl//.
- by rewrite (_ : (_ \x _)%E = giry_prod P)// fin_num_measure.
- exact: measurableC.
Qed.

(* See: Tobias Fritz. A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics.
   https://arxiv.org/abs/1908.07021 *)
Lemma measurable_giry_prod :
  measurable_fun [set: giry T1 R * giry T2 R] giry_prod.
Proof.
apply: measurable_giry_codensity => /=.
rewrite measurable_prod_measurableType.
apply: dynkin_induction => /=.
- by rewrite measurable_prod_measurableType.
- move=> _ _ [A1 mA1 [A2 mA2 <-]] [B1 mB1 [B2 mB2 <-]].
  exists (A1 `&` B1); first exact: measurableI.
  exists (A2 `&` B2); first exact: measurableI.
  by rewrite setXI.
- apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      x.1 [set: T1] * x.2 [set: T2])).
    by move=> x _; rewrite -setXTT product_measure1E.
  by apply: emeasurable_funM => /=;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> _ [A mA [B mB <-]].
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R => x.1 A * x.2 B)).
    by move=> x _; rewrite product_measure1E.
  by apply: emeasurable_funM;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> S mS HS.
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      x.1 [set: T1] * x.2 [set: T2] - (x.1 \x x.2) S)).
    move=> /= x _; rewrite subprobability_prod_setC//.
    by rewrite -setXTT product_measure1E.
  apply emeasurable_funB => //=.
  by apply: emeasurable_funM => //=;
    apply: (@measurableT_comp _ _ _ _ _ _ (giry_ev ^~ _)) => //;
    exact: measurable_giry_ev.
- move=> F mF tF Fn.
  apply: (eq_measurable_fun (fun x : giry T1 R * giry T2 R =>
      \sum_(0 <= k <oo) (x.1 \x x.2) (F k))).
    by move=> x _; rewrite measure_semi_bigcup//; exact: bigcup_measurable.
  exact: ge0_emeasurable_sum.
Qed.

End measurable_giry_prod.

Section giry_prod_int.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}
  {R : realType}.
Variables (μ1 : giry T1 R) (μ2 : giry T2 R) (h : T1 * T2 -> \bar R).
Hypotheses (mh : measurable_fun [set: T1 * T2] h) (h0 : forall x, 0 <= h x).

Lemma giry_int_prod1 : giry_int (giry_prod (μ1, μ2)) h =
  giry_int μ1 (fun x => giry_int μ2 (fun y => h (x, y))).
Proof. exact: fubini_tonelli1. Qed.

Lemma giry_int_prod2 : giry_int (giry_prod (μ1, μ2)) h =
  giry_int μ2 (fun y => giry_int μ1 (fun x => h (x, y))).
Proof. exact: fubini_tonelli2. Qed.

End giry_prod_int.
