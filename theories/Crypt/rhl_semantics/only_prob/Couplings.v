From SSProve.Mon Require Import FiniteProbabilities SPropMonadicStructures SpecificationMonads MonadExamples SPropBase FiniteProbabilities.
From Coq Require Import RelationClasses Morphisms.
From SSProve.Relational Require Import OrderEnrichedCategory OrderEnrichedRelativeMonadExamples Commutativity.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals measure classical_sets.
From mathcomp Require Import fsbigop functions reals separation_axioms.
From mathcomp Require Import ereal sequences numfun measure measurable_realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms ChoiceAsOrd only_prob.SubDistr.

From SSProve Require Import giry.
From HB Require Import structures.

Import SPropNotations.
Import Num.Theory.

Local Open Scope ring_scope.

(*so that Next Obligation doesnt introduce variables by itself:*)
Obligation Tactic := try (Tactics.program_simpl ; fail) ; simpl.

(*
In this file we develop a simple theory of couplings: their interaction
with the ret and bind operators of the SDistr relative monad, and
the product coupling for subdistributions that have a sum < 1
(some normalization is required).
*)

  Lemma eqType_lem : forall (Z : eqType) (z t : Z), z = t \/ ~(z = t).
  Proof.
    intros Z z t. case Hzt : (z==t).
    left. move: Hzt => /eqP. trivial.
    right. move: Hzt => /eqP. trivial.
  Qed.

  Lemma refl_true : forall (Z : eqType) (z :Z), (z == z) = true.
  Proof.
    intros. apply /eqP. reflexivity.
  Qed.

  Lemma reflection_nonsense : forall (Z : eqType) (a x : Z), (a == x) = true -> a = x.
  Proof.
  intros Z a x. intro Hax. unshelve eapply elimT. exact (a == x).
  apply eqP. assumption.
  Qed.



#[short(type=count1Type)]
HB.structure Definition Countable1 := {T of isPointed T & Countable T}.

HB.instance Definition _ := Pointed.on bool.

Check (bool : count1Type).

Section Coupling_def.
  (*Context {A1 A2 : ord_choiceType}.*)
  Context {A1 A2 : count1Type}.

  Definition unprodD {A B : pointedType} : D (A * B) -> D A * D B
    := fun a => a.

  Definition prodD {A B : pointedType} : (D A * D B) -> D (A * B)
    := fun a => a.

  Definition d' {A : pointedType} : D A -> A := id.

  Lemma measurable_D {d} {A : measurableType d} : measurable_fun setT (@d' A).
  Proof.
    done.
  Qed.

  Lemma measurable_unprod {A B : pointedType} :
    measurable_fun setT (@unprodD A B).
  Proof. done. Qed.

  (*
  Lemma prodD_prod {A B : Type} {Y : set (A * B)}
     : (prodD @^-1` Y) = \bigcup[xy \in Y] xy.
   *)

  (*
  About pointedType.
  HB.howto pointedType.
  HB.pointedCountType
   *)

  Lemma measurable_prodD {A B : count1Type} : measurable_fun setT (@prodD A B).
  Proof.
    intros S Y _.
    simpl in *.
    rewrite setTI /prodD preimage_id.
    replace Y with (\bigcup_(y : (A * B)) if y \in Y then [set y] else set0)%classic.
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

  Definition giry_fst {d d'} {T : measurableType d} {T' : measurableType d'}
    : giry (T * T')%type R -> giry T R
    := fun a => giry_map measurable_fst a.

  Definition D_fst' {A B : pointedType}
    : giry (D (A * B)%type) R -> giry (D A) R
    := fun a => giry_fst (giry_map measurable_unprod a).

  Program Definition D_fst {A B : pointedType}
    : giry (D (A * B)%type) R -> giry (D A) R
    := fun gab => giry_map (f := fun ab : D (A * B)%type => ab.1 : D A) _ gab.
  Obligation 1. done. Qed.


  Definition lmg :
  TypeCat ⦅ SDistr( F_choice_prod (npair A1 A2) ) ; SDistr( A1 )  ⦆
    := D_fst.

  Definition giry_snd {d d'} {T : measurableType d} {T' : measurableType d'}
    : giry (T * T')%type R -> giry T' R
    := fun a => giry_map measurable_snd a.

  Definition D_snd' {A B : pointedType}
    : giry (D (A * B)%type) R -> giry (D B) R
    := fun a => giry_snd (giry_map measurable_unprod a).

  Program Definition D_snd {A B : pointedType}
    : giry (D (A * B)%type) R -> giry (D B) R
    := fun gab => giry_map (f := fun ab : D (A * B)%type => ab.2 : D B) _ gab.
  Obligation 1. done. Qed.

  Program Definition D_prod_cst {A B : pointedType}
  : A -> giry (D B) R -> giry (D (A * B)%type) R
  (*:= fun a gb => giry_map (f := fun b => (a, b) : D _) _ gb.*)
    := fun a gb => giry_bind gb (f := fun b => @giry_ret _ (D _) _ (a, b)) _.
  Obligation 1. intros. done. Qed.

  Program Definition D_prod {A B : count1Type}
    : giry (D A) R * giry (D B) R -> giry (D (A * B)%type) R
    (*:= fun x => giry_bind x.1 (f := fun a => D_prod_cst a x.2) _.*)
    := fun x => giry_map measurable_prodD (giry_prod x).

  Definition rmg :
  TypeCat ⦅ SDistr( F_choice_prod (npair A1 A2) ) ; SDistr( A2 )  ⦆
    := D_snd.

  Definition coupling (d : SDistr( F_choice_prod (npair A1 A2) ) )
  (c1 : SDistr A1) (c2 : SDistr A2) : Prop := (lmg d = c1) /\ (rmg d = c2).

  Lemma giry_eq
    {d d'} {T : measurableType d} {T' : measurableType d'}
    {a : T} {b : T'}
    : giry_prod (giry_ret a, giry_ret b) = giry_ret (a, b) :> giry (T * T')%type R.
  Proof.
    apply eq_subprobability => S /=.
    rewrite diracE /product_measure1 //=.
    rewrite integral_dirac //.
    rewrite diracT.
    rewrite diracE.
    rewrite mem_xsection mul1e //.
  Admitted.

  Lemma giry_eq' {a : D A1} {b : D A2}
    : giry_prod (giry_ret a, giry_ret b) = giry_ret (a, b) :> giry (D A1 * D A2)%type R.
  Proof.
    apply eq_subprobability => S /=.
    rewrite diracE /product_measure1 //=.
    rewrite integral_dirac //.
    rewrite diracT.
    rewrite diracE.
    rewrite mem_xsection mul1e //.
  Qed.

  Lemma giry_eq'' {a : A1} {b : A2}
    : D_prod (@giry_ret _ (D A1) _ a, @giry_ret _ (D A2) _ b)
    = @giry_ret _ (D (A1 * A2)%type) _ (a, b) :> giry (D (A1 * A2)%type) R.
  Proof.
    apply eq_subprobability => S /=.
    rewrite giry_int_map //=.
    2: apply measurable_giry_ev; admit.
    rewrite giry_int_ret //.
  Admitted.
  Search giry_prod.

  Lemma asedflk {A B : pointedType} {ab : giry (D A) R * giry (D B) R} {F : set (D (A * B))}
  (*: D_prod ab F = giry_int ab.1 (fun x => giry_int ab.2 (fun y => giry_ret (x, y) F)).*)
    : D_prod ab F = giry_int (giry_prod ab) (fun xy => giry_ret xy F).
  Proof.
    destruct ab as [a b].
    rewrite giry_int_prod1 /D_prod //=.
    rewrite giry_int_map.
    (*2: apply measurable_giry_ret.*)
  Admitted.

  Lemma asdfs {ab : giry (D (A1 * A2)) R} : giry_prod (D_fst ab, D_snd ab) = giry_map measurable_unprod ab.
  Proof. Admitted.

  Lemma giry_eq2 {ab : giry (D (A1 * A2)) R}
    : D_prod (D_fst ab, D_snd ab) = ab.
  Proof.
    apply eq_subprobability => S.
    rewrite asedflk asdfs.
    rewrite giry_int_map //=.
    (*Search "unique" "measure".*)
    2: apply measurable_fun_dirac; admit.
    rewrite giry_fst.
    simpl.
    simpl.
    rewrite giry_mapE //.
    Search giry_prod.
    Search giry_int giry_prod.
    rewrite -giry_int_prod1.

    rewrite giry_int_2.
    unfold giry_ev.

    rewrite -giry_int_prod1.
    Search giry_int.
    Search giry_int.
    rewrite giry_mapE //.
    Search giry_map.
    rewrite giry_mapE.

    rewrite giry_int_map //.
    2: apply measurable_giry_ev; admit.
    rewrite giry_int_map //.

    unfold giry_int.
    simpl.
    unfold pushforward.
    simpl.
    apply eq_integral.
    2: apply measurable_giry_ev; admit.
    Search giry_prod.
    unfold D_fst.

  (*
  Lemma giry_eq
    {d d'} {T : measurableType d} {T' : measurableType d'} {ab}
    : giry_prod (giry_fst ab, giry_snd ab) = ab :> giry (T * T')%type R.
  Proof.
    apply eq_subprobability => S /=.
    unfold product_measure1.
    rewrite integral_pushforward //=.
    Search "fubini".
    unfold pushforward.
    under eq_integral.
    1: intros; rewrite -setTX; over.
    Search giry_prod.
    Search xsection.
    Search (setT `*` _)%classic.
    1: intros; rewrite xsectionE /=.
    Search (_ @^-1` _)%classic.
    rewrite preimage_
    rewrite xsection_preimage_snd.
    Search pushforward.
    rewrite pushforwardE.

    replace (ab S) with (\int[ab]_(x in S) cst 1 x)%E.
    Search giry.
    Search integral cst.
    2: rewrite integral_cst ?mul1e //.
    2: admit.
    
    Search integral \1__.
    2: rewrite int
    Search dirac integral.
    Check integral.
    unfold pushforward.

    rewrite xsectionE.
    Search xsection.
    Search pushforward.
    rewrite pushforwardE.
    Search (\int[_]__ )%E.
    Search (\1__).
    Search giry_ev.
    generalize S.
    eapply dynkin_induction => //.
    rewrite measureU.
    Check measureU.
    Search pushforward.
    simpl.
    
    unfold giry_prod.
    simpl.

  Lemma dirac_prodE {T T' : pointedType}
    {x : D T} {y : D T'} : (\d_x \x \d_y)%E = \d_(x, y) :> giry (T * T') subprobability  R.
  Proof.
    apply eq_subprobability.
    intros S.
    rewrite diracE /product_measure1 //=.
    rewrite integral_dirac //.
    rewrite diracT.
    rewrite diracE.
    rewrite mem_xsection mul1e //.
  Qed.

   *)

End Coupling_def.

Section Weight_of_SDistr_unit.
  Context {A : ord_choiceType} (a : A).

  Lemma psum_SDistr_unit : giry_ev (SDistr_unit A a) setT = 1%E.
  Proof. rewrite //= diracE in_setT //. Qed.

End Weight_of_SDistr_unit.


Section Couplings_vs_ret.

  Context {A1 A2 : count1Type}.
  (*Context {A1 A2 : ord_choiceType}.*)
  Context (a1 : A1) (a2 : A2) (d : SDistr( F_choice_prod (npair A1 A2) )).

  (*the left and right marginals of the unit coupling are the units for
  left and right types*)
  Lemma SDistr_unit_F_choice_prod_coupling :
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2) ->
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2).
  Proof.
    intro Hunit. subst. split.
    - by apply eq_subprobability.
    - by apply eq_subprobability.
  Qed.

  (*
  Lemma lmg_SDistr_unit :
  lmg d = SDistr_unit A1 a1 ->
  forall (x1 : A1) (x2 : A2), ~(a1 = x1) -> d (set1 (x1,x2)) = 0.
  Proof.
    intro rHcoupl. intros x1 x2. intro Hxa.
    unfold lmg in rHcoupl. unfold SDistr_unit in rHcoupl.
    assert (rHcoupl1 : D_fst d (set1 x1) = giry_ret (a1 : D A1) (set1 x1)).
      rewrite rHcoupl. reflexivity.
    rewrite //= diracE in rHcoupl1.

    simpl in rHcoupl1.
    rewrite D_fst in rHcoupl1.
    rewrite (dfstE d x1) (dunit1E a1 x1) in rHcoupl1.
    assert ((a1==x1 = false)).
      apply /eqP. assumption.
    rewrite H /= in rHcoupl1.
    epose (bla := eq0_psum _ rHcoupl1 x2).
    apply bla. Unshelve.
      eapply summable_fst.
  Qed.

  Lemma rmg_SDistr_unit :
  rmg d = SDistr_unit A2 a2 ->
  forall (x1 : A1) (x2 : A2), ~(a2 = x2) -> d(x1,x2) = 0.
  Proof.
    intro rHcoupl. intros x1 x2. intro Hxa.
    unfold rmg in rHcoupl. unfold SDistr_unit in rHcoupl.
    assert (rHcoupl1 : dsnd d x2 = dunit (T:=A2) a2 x2).
      rewrite rHcoupl. reflexivity.
    rewrite (dsndE d x2) (dunit1E a2 x2) in rHcoupl1.
    assert ((a2==x2 = false)).
      apply /eqP. assumption.
    rewrite H /= in rHcoupl1.
    epose (bla := eq0_psum _ rHcoupl1 x1).
    apply bla. Unshelve.
      eapply summable_snd.
  Qed.

  Lemma lmg_rmg_SDistr_unit
  (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2)) :
  forall (x1 : A1) (x2 : A2), ~( (x1,x2) = (a1,a2) ) -> d(x1,x2) = 0.
  Proof.
    intros. move: hCoupl => [lH rH].
    case HXA : (x1 != a1).
      - eapply lmg_SDistr_unit. assumption. unshelve eapply elimT in HXA.
        exact (~(x1 = a1)). intro. symmetry in H0. apply HXA. assumption.
        eapply Bool.iff_reflect. split.
          intro. assumption.
          intros. intro. rewrite H1 in HXA. move: HXA => /negP HXA.
          apply HXA. apply /eqP. reflexivity.
      -  unshelve eapply introN in H. exact ((x1,x2)==(a1,a2)). all: revgoals. apply eqP.
         simpl in H.
         unfold "==" in H. simpl in H. rewrite Bool.negb_andb in H.
         rewrite HXA in H. simpl in H.
        eapply rmg_SDistr_unit. assumption. move: H => /negP H.
        intro Ha2x2. rewrite Ha2x2 in H. apply H. apply /eqP. reflexivity.
  Qed.
   *)

  (*
  Lemma weight_from_mgs (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2)):
  giry_ev d setT = 1%E.
  Proof.
    move: hCoupl => [H1 H2].
    simpl.
    rewrite hCoupl
    rewrite hCoupl.
    re
    done.
    rewrite (@psum_coupling_left A1 A2 d (SDistr_unit A1 a1) (SDistr_unit A2 a2) hCoupl).
    eapply psum_SDistr_unit.
  Qed.
   *)

  (*
  Lemma d_is_one
  (hCoupl : coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2))  :
  d(a1,a2) = 1.
  Proof.
    unshelve epose (@psum_finseq R (F_choice_prod (npair A1 A2)) d [::(a1,a2)] _ _).
      rewrite cons_uniq //=.
      move=> [x1 x2]. unfold in_mem. simpl.
      intro Hsupp. apply /orP. left.
      move: Hsupp. apply contraLR. intro Hxadiff. unfold "==". simpl.
      rewrite Bool.negb_involutive. rewrite -/(_ == _).
      apply /eqP. unshelve eapply lmg_rmg_SDistr_unit. assumption.
      move: Hxadiff => /negP Hxadiff. intro bla. rewrite bla in Hxadiff.
      apply Hxadiff. apply eq_refl.
      move: e. rewrite big_seq1. move=> e. rewrite weight_from_mgs in e.
      rewrite e. symmetry. assert (Hbnorm: `|d (a1, a2)| == d (a1, a2) -> `|d (a1, a2)| = d (a1, a2)).
      move=> /eqP. trivial.
      apply Hbnorm. rewrite -(ger0_def). destruct d as [d1 d2 d3 d4]. simpl in *.
      apply (d2 (a1,a2)). assumption.
  Qed.

  Lemma coupling_SDistr_unit_F_choice_prod :
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2) ->
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2).
  Proof.
    simpl in *. unfold SDistr_carrier in d.
    move=> hCoupl.
    apply distr_ext. move=> [x1 x2]. unfold SDistr_unit.
    assert (xa_lem : (x1,x2) = (a1,a2) \/ ~((x1,x2) = (a1,a2))).
      apply eqType_lem.
    destruct xa_lem as [xa_lem_left | xa_lem_right].
      rewrite dunit1E. rewrite xa_lem_left. rewrite refl_true. simpl.
      unshelve eapply d_is_one. assumption.
    rewrite dunit1E. assert ((a1, a2) == (x1, x2) = false).
    apply Bool.negb_true_iff. apply /negP. move=> /eqP hxa. symmetry in hxa.
    apply xa_lem_right. assumption.
    rewrite H. simpl. unshelve eapply lmg_rmg_SDistr_unit. assumption.
    assumption.
  Qed.
   *)

  Lemma measurable_prod {A B : pointedType} :
    measurable_fun setT (@prodD A B).
  Proof. done. Qed.

  (*
  Definition D_prod {A B : pointedType}
    : giry (D A) R * giry (D B) R -> giry (D (A * B)%type) R
    := fun a => giry_map measurable_prod (giry_prod a).
   *)

  (*
  Lemma testtt {x y} {A : measurableType x} {B : measurableType y}
    {ab : D (A * B)}
    : giry_prod (D_fst (giry_ret ab), D_snd (giry_ret ab)) = giry_ret ab.
  Proof.
    apply eq_subprobability => z.
    simpl.
    rewrite diracE.
    Search (_ \x _)%E.
    Search pushforward.
  Admitted.

   *)

  Lemma coupling_vs_ret :
        d = SDistr_unit (F_choice_prod (npair A1 A2)) (a1,a2) <->
        coupling d (SDistr_unit A1 a1) (SDistr_unit A2 a2).
  Proof.
    split.
    - intro dCoupl. unshelve eapply SDistr_unit_F_choice_prod_coupling.
      assumption.
    -
      unfold SDistr_unit.
      move=> [H1 H2].
      rewrite -giry_eq''.
      rewrite -H1 -H2.
      unfold lmg, rmg.
      apply eq_subprobability => S.
      simpl.
      rewrite giry_int_map //=.
      2: apply measurable_giry_ev; admit.
      rewrite giry_mapE.
      unfold D_fst.
      rewrite giry_int_map //=.
      apply eq_integral => //=.
      2: apply measurable_id.
      2: admit.
      intros [x y] _.
      simpl.
      unfold pushforward.
      Search pushforward.
      rewrite pushforward.
      
      simpl.

      unfold giry_int.

      unfold "\o".
      unfold giry_int.
      under eq_integral.
      1: intros.
      unfold giry_ev, D_prod_cst.
      rewrite giry_mapE //.
      over.
      simpl.
      un
      Search giry_int.
      Search giry_int eq.
      simpl.
      unfold pushforward.
      unfold D_prod_cst.
      simpl.
      done.

      unfold giry_int.
      Search giry_int eq.
      rewrite giry_intE.
      rewrite giry_map_comp.
      rewrite giry_int_map //=.
      Search giry_int.
      2: eapply (measurable_comp _ _ (measurable_giry_ev _)).
      2: unfold D_prod_cst.
      2: eapply measurable_giry_map.
      2: done.

      2: apply measurable_giry_ev; admit.

      rewrite /D_fst giry_int_ret.

      Set Printing All.
      rewrite -(@giry_eq' A1 A2 a1 a2).
      unfold lmg, D_fst in H1.
      unfold rmg, D_snd in H2.
      simpl.
      simpl in *.
      change a1 with (a1 : D A1).
      change a2 with (a2 : D A2).
      Set Printing All.
      rewrite -(@dirac_prodE A1 A2 a1 a2 S).
      change (\d_(a1, a2)) with (\d_(a1 : D A1, a2 : D A2)).
      Search giry_map.
      change d with (giry_prod (D_fst d, D_snd d)).
      Set Printing All.
      replace (@giry_ret _ (D (D A1 * D A2)) R (a1, a2))
        with (giry_prod (@giry_ret _ (D A1) _ a1, @giry_ret _ (D A2) _ a2)).
      replace d with (giry_prod (giry_ret a1, giry_ret b)).
      rewrite -testtt.
      simpl in H1, H2.
      Set Printing Implicit.
      simpl.
      unfold F_choice_prod_obj.
      simpl.

      replace d with (D_prod (D_fst d, D_snd d)).
      2: unfold D_prod, D_fst, D_snd.
      2: admit.
      unfold lmg in H1.
      unfold rmg in H2.
      rewrite H1 H2.
      apply eq_subprobability => S.
      unfold D_prod.
      rewrite giry_mapE //=.
      rewrite -fubini2 //=.
      1: rewrite integral_dirac //=.
      unfold fubini_G. simpl.
      1: rewrite integral_dirac //=.
      rewrite diracE.
      rewrite diracE.
      rewrite diracE.
      rewrite -EFinM -2!GRing.Theory.natrM.
      rewrite 2!mulnb.
      do 2 f_equal.
      1: admit.
      Search (_.-integrable).
      apply /integrableP.
      Search measurable_fun.
      split.
      1: apply /prod_measurable_funP.
      Search prod measurable_fun.
      1: apply measurable_product.
      1: apply measurable_fun_dirac.
      apply integrable_indic.
      Search dirac.
      simpl.

      rewrite G
      1: rewrite integral_dirac //=.

      Search integral product_measure1.
      Search dirac i
      Search  (_ \x _)%E.
      rewrite integral_dirac.
      rewrite diracE.
      
      simpl.
      Search giry_prod.
      unfold giry_map.
      rewrite giry_mapE //=.
      rewrite fubini_tonelli2 //.
      rewrite Fubini.
      rewrite integral_prod.
      Search dirac integral.
      rewrite diracE int_dirac.
      simpl in d.
      Check (giry_prod (D_fst d, D_snd d)).
      simpl.
      rewrite diracE.
      Search dirac.
      unfold giry_ret.
      destruct d.
      simpl.
      un

      
      unshelve eapply coupling_SDistr_unit_F_choice_prod.
       assumption.
  Qed.

End Couplings_vs_ret.

Lemma msupp : forall A1 A2 s s0 (dA : SDistr _), (s, s0) \in dinsupp (T:=F_choice_prod ⟨ A1, A2 ⟩) dA -> 0 < dA (s, s0) = true.
Proof.
  move=> A1 A2 a1 a2 dA. move=> Hdinsupp. rewrite /in_mem in Hdinsupp.
  simpl in Hdinsupp. rewrite /dinsupp in Hdinsupp. rewrite lt0r.
  apply /andP. split. all: revgoals.
    move: dA Hdinsupp => [dAmap dAz dASumbl dAPsum]. simpl.
    move=> Hdinsupp. apply dAz.
  assumption.
Qed.

Section Couplings_vs_bind.
  Context {A1 A2 B1 B2 : ord_choiceType}.

  Context (c1 : SDistr A1) (f1 : TypeCat ⦅ choice_incl A1 ; SDistr B1⦆ )
  (c2 : SDistr A2) (f2 : TypeCat ⦅ choice_incl A2 ; SDistr B2⦆).

  Context (dA : SDistr ( F_choice_prod (npair A1 A2) ) ) (dA_coup : coupling dA c1 c2).

  Context (kd : TypeCat ⦅ choice_incl (F_choice_prod (npair A1 A2)) ; SDistr (F_choice_prod( npair B1 B2)) ⦆)
          (kd_pcoup : forall (x1 : A1) (x2 : A2), (dA (x1, x2) > 0) = true -> coupling (kd (x1,x2)) (f1 x1) (f2 x2)  ).

  Lemma coupling_vs_bind :
  coupling (SDistr_bind (F_choice_prod(npair A1 A2)) (F_choice_prod(npair B1 B2)) kd dA)
           (SDistr_bind A1 B1 f1 c1) (SDistr_bind A2 B2 f2 c2).
  Proof. split.
         -  unfold lmg.
            unfold SDistr_bind.
            unfold dfst.
            move: dA_coup.
            rewrite /coupling /lmg.
            intros [H1 H2].
            rewrite <- H1.
            unfold dfst.
            apply distr_ext. intro b.
            rewrite (dlet_dlet kd (fun x => dunit x.1) dA).
            rewrite (dlet_dlet _ _ dA).
            apply (@eq_in_dlet _ _ _).
            move => x12 Hsupp b2.
            destruct x12.
            simpl. rewrite (dlet_unit).
            assert (0 < dA (s, s0) = true).
            apply msupp. assumption.
            specialize (kd_pcoup s s0 H).
            unfold coupling in kd_pcoup. destruct kd_pcoup.
            unfold lmg in H0. unfold dfst in H0.
            rewrite H0. reflexivity.
            intro x. reflexivity.
         -  unfold rmg.
            unfold SDistr_bind.
            unfold dfst.
            move: dA_coup.
            rewrite /coupling /lmg.
            intros [H1 H2].
            rewrite <- H2.
            unfold dfst.
            apply distr_ext. intro b.
            rewrite (dlet_dlet kd (fun x => dunit x.2) dA).
            rewrite (dlet_dlet _ _ dA).
            apply (@eq_in_dlet _ _ _).
            move => x12 Hsupp b2.
            destruct x12.
            simpl. rewrite (dlet_unit).
            assert (0 < dA (s, s0) = true).
            apply msupp. assumption.
            specialize (kd_pcoup s s0 H).
            unfold coupling in kd_pcoup. destruct kd_pcoup.
            unfold rmg in H3. unfold dfst in H3.
            rewrite H3. reflexivity.
            intro x. reflexivity.
Qed.

End Couplings_vs_bind.


(*the rest of the file is work in progress*)

Section Forall_exists.
  (*work in progress *)

  Context {A1 A2 B1 B2 : ord_choiceType}.

  Context (c1 : SDistr A1) (f1 : TypeCat ⦅ choice_incl A1 ; SDistr B1⦆ )
  (c2 : SDistr A2) (f2 : TypeCat ⦅ choice_incl A2 ; SDistr B2⦆).

  Context (dA : SDistr ( F_choice_prod (npair A1 A2) ) ) (dA_coup : coupling dA c1 c2).

  Context (q : A1 -> A2 -> (SDistr ( F_choice_prod (npair B1 B2) )) -> Prop).

  Lemma Forall_vs_exists
  ( all_ex :  forall(a1 : A1) (a2 : A2), exists (dB : SDistr ( F_choice_prod (npair B1 B2) )),
  coupling dB (f1 a1)(f2 a2) /\ (q a1 a2 dB)   ) :
  exists (kd : TypeCat ⦅ choice_incl (F_choice_prod (npair A1 A2)) ; SDistr (F_choice_prod( npair B1 B2)) ⦆)  ,  (forall (x1 : A1) (x2 : A2), coupling (kd (x1,x2)) (f1 x1) (f2 x2)  ) /\
  forall a1 a2, q a1 a2 (kd (a1,a2)).
  Proof.
  unshelve esplit.
  -  move=> [a1 a2]. move: (all_ex a1 a2). Fail move=> [dB dBcoup].
     move=> dBex.
     apply boolp.constructive_indefinite_description in dBex.
     move: dBex => [dB [dBcoup dBq]]. exact dB.
  intuition.
  -  move: (all_ex x1 x2) => from_all_ex.
  destruct from_all_ex as [kdx1x2 kdcoupq]. simpl.

 Abort.


End Forall_exists.

(* Section Independent_coupling. *)
(*   (*work in progress*) *)

(*   Context {A1 A2 : ord_choiceType}. *)

(*   Context (c1 : SDistr A1) (c2 : SDistr A2). *)

(*   Definition indp := SDistr_bind _ _ (fun x => SDistr_bind _ _ (fun y => SDistr_unit _ (x, y)) c2) c1. *)

(*   Local Lemma indp_ext (x : A1) (y : A2) : indp (x, y) = c1 x * c2 y. *)
(*   Proof. *)
(*     unfold indp. *)
(*     unfold SDistr_bind, SDistr_unit. *)
(*     rewrite dletE. *)
(*     assert ((fun x0 : A1 => c1 x0 * (\dlet_(y0 <- c2) dunit (T:=prod_choiceType A1 A2) (x0, y0)) (x, y)) = (fun x0 : A1 => c1 x0 * psum (fun y0 : A2 => c2 y0 * dunit (T:=prod_choiceType A1 A2) (x0, y0)  (x, y)))) as H. *)
(*     { extensionality x0. rewrite dletE. reflexivity. } *)
(*     rewrite H. clear H. *)
(*     assert ((fun x0 : A1 => *)
(*                c1 x0 * psum (fun y0 : A2 => c2 y0 * dunit (T:=prod_choiceType A1 A2) (x0, y0) (x, y))) = *)
(*             (fun x0 : A1 => *)
(*                psum (fun y0 : A2 => c1 x0 * c2 y0 * (dunit (x0, y0) (x, y))))). *)
(*     { extensionality x0. *)
(*       rewrite -psumZ. *)
(*       2: { admit. } *)
(*       apply f_equal. *)
(*       extensionality y0. *)
(*       simpl. rewrite dunit1E. *)
(*       apply GRing.mulrA. } *)
(*     rewrite H. clear H. *)
(*     rewrite -(psum_pair (S := fun p => c1 (fst p) * c2 (snd p) * dunit p (x, y))). *)
(*   Admitted. *)

(*   Local Lemma independent_coupling_lmg : lmg indp = c1. *)
(*   Proof. *)
(*   Admitted. *)

(*   Local Lemma independent_coupling_rmg : rmg indp = c2. *)
(*   Proof. *)
(*   Admitted. *)

(*   Local Lemma independent_coupling : coupling indp c1 c2. *)
(*   Proof. *)
(*     unfold coupling. *)
(*     split. *)
(*     - apply independent_coupling_lmg. *)
(*     - apply independent_coupling_rmg. *)
(*   Qed. *)
(* End Independent_coupling. *)
