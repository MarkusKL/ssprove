From Coq Require Import Utf8.

From mathcomp Require Import all_ssreflect ssreflect eqtype choice seq ssrfun ssrbool finmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

#[local] Open Scope fset.
#[local] Open Scope fmap.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Section Defs.
  Context {K : choiceType} {V V' : Type}.
  (* Note that submapf is defined into Prop unlike other extructures operators.
     A bool definition would require S to be an eqType, which would make it
     hard to have maps into e.g. Type or choiceType. *)
  Definition submapf (m m' : {fmap K → V}) : Prop
    := m' + m = m'. (* alt: m'.[& domf m ] = m. *)

  Definition hasf (m : {fmap K → V}) k v
    := m.[k <- v] = m. (* alt: m.[? k] = Some v *)

  (* implied by disjointness *)
  Definition compatf (m m' : {fmap K → V}) :=
    m + m' = m' + m.  (* alt: m.[& domf m'] = m'.[& domf m]. *)

  Inductive separatef
    (m : {fmap K → V}) (m' : {fmap K → V'}) :=
    | fsep : [disjoint domf m & domf m'] → separatef m m'.

End Defs.

Context {K : choiceType} {K' : choiceType} {V V' V'' : Type}.

Lemma submapf_hasf (m m' : {fmap K → V}) k v
  : submapf m m' → hasf m k v → hasf m' k v.
Proof. intros H H'. rewrite /hasf -H -catf_setr H' //. Qed.

Lemma catfI (m : {fmap K → V}) : m + m = m.
Proof.
  apply fmapP => k.
  rewrite fnd_cat.
  by elim: (k \in domf m).
Qed.

Lemma submapfUl (m m' : {fmap K → V}) : compatf m m' → submapf m (m + m').
Proof. intros H. rewrite /submapf -catfA -H catfA catfI //. Qed.

Lemma submapfUr (m m' : {fmap K → V}) : submapf m' (m + m').
Proof. rewrite /submapf -catfA catfI //. Qed.

Lemma submapf_trans (m m' m'' : {fmap K → V}) :
  submapf m m' → submapf m' m'' → submapf m m''.
Proof.
  intros H H'.
  apply fmapP => k.
  rewrite -H' -H -2!catfA catfI //.
Qed.

Lemma submapfUl_trans (m m' m'' : {fmap K → V}) :
  compatf m' m'' → submapf m m' → submapf m (m' + m'').
Proof.
  intros H H'. eapply submapf_trans;
  [ apply H' | apply submapfUl, H ].
Qed.

Lemma submapfUr_trans (m m' m'' : {fmap K → V}) :
  submapf m m'' → submapf m (m' + m'').
Proof.
  intros H. eapply submapf_trans;
  [ apply H | apply submapfUr ].
Qed.

Lemma subUmapf (m m' m'' : {fmap K → V}) :
  submapf m m'' → submapf m' m'' → submapf (m + m') m''.
Proof. intros H H'. rewrite /submapf catfA H H' //. Qed.

Lemma sub0mapf (m : {fmap K → V}) : submapf fmap0 m.
Proof. rewrite /submapf catf0 //. Qed.

Lemma hasf0 (k : K) (v : V) : ¬ hasf fmap0 k v.
Proof.
  rewrite /hasf -fmapP.
  intros H.
  specialize (H k).
  rewrite fnd_fmap0 fnd_set eq_refl // in H.
Qed.

Lemma hasf_set (m : {fmap K → V}) k v :
  hasf (m.[k <- v]) k v.
Proof. rewrite /hasf setfC eq_refl //. Qed.

Lemma hasf_set_next (m : {fmap K → V}) k k' v v' :
  k ≠ k' → hasf m k v → hasf (m.[k' <- v']) k v.
Proof.
  move=> /eqP H H'.
  rewrite /hasf setfC H'.
  destruct (k == k') => //.
Qed.

Lemma submapfxx (m : {fmap K → V}) : submapf m m.
Proof. rewrite /submapf catfI //. Qed.

Lemma hasf_set_case (m : {fmap K → V}) k v k' v' :
  hasf m.[k <- v] k' v' → v = v' ∨ hasf m k' v'.
Proof.
  intros H.
  rewrite /hasf setfC in H.
  destruct (k' == k) eqn:E.
  - left.
    rewrite -fmapP in H.
    specialize (H k).
    move: E => /eqP E; subst.
    rewrite 2!fnd_set eq_refl in H.
    by noconf H.
  - right.
    (*
    rewrite /hasf -2!fmapP in H |- *.
    specialize (H k
    unfold hasf.
    rewrite -setf_rem1 -(setf_rem1 m k) in H.
    apply setf_inj in H.
    Search setf.
    Search "inj" setf.
     *)
  (*
  rewrite /hasf setfC in H.
  - left.
    by noconf H.
  - by right.
Qed.
   *)
Admitted.

(* Tactics *)

Ltac fmap_invert H :=
  (by apply hasf0 in H) ||
  ( let x := fresh "x" in
    apply hasf_set_case in H ;
    destruct H as [x|H]; [ noconf x | fmap_invert H ]
  ).

Create HintDb fmap_solve_db.

#[export] Hint Extern 2 (hasf ?m ?k) =>
  apply hasf_set
  : fmap_solve_db.

#[export] Hint Extern 3 (hasf ?m ?k) =>
  apply hasf_set_next; [ done |]
  : fmap_solve_db.

#[export] Hint Resolve submapfUl_trans submapfUr_trans
  : fmap_solve_db.

#[export] Hint Extern 1 (compatf ?m ?m') =>
  reflexivity
  : fmap_solve_db.

Hint Extern 1 (submapf ?m ?m') =>
  apply submapfxx
  : fmap_solve_db.
  

Ltac fmap_solve :=
  typeclasses eauto with fmap_solve_db.


Definition compatf11 (k : K) (v : V) k' v'
  := k ≠ k' ∨ v = v'.

Lemma compatf0m (m : {fmap K → V})
  : compatf fmap0 m.
Proof. rewrite /compatf catf0 cat0f //. Qed.

Lemma compatfm0 (m : {fmap K → V})
  : compatf m fmap0.
Proof. rewrite /compatf catf0 cat0f //. Qed.

Lemma compatf11_swap (k : K) (v : V) k' v' m
  : compatf11 k v k' v'
  → m.[k' <- v'].[k <- v] = m.[k <- v].[k' <- v'].
Proof.
  intros [H|H].
  - rewrite setfC.
    move: H => /eqP /negPf -> //.
  - destruct (k == k') eqn:E.
    + move: E H => /eqP.
      intros ? ?. by subst.
    + rewrite setfC E //.
Qed.

Lemma compatf_set (k : K) (v : V) k' v' m
  : compatf11 k v k' v'
  → compatf [fmap].[k <- v] m
  → compatf [fmap].[k <- v] m.[k' <- v'].
Proof.
  intros H H'.
  rewrite /compatf 2!catf_setr H' catf_setr 2!catf0.
  rewrite -compatf11_swap //.
Qed.

Lemma compatf_set_set k v k' v' (m m' : {fmap K → V})
  : compatf [fmap].[k <- v] m'
  → compatf m.[k' <- v'] m'
  → compatf m.[k' <- v'].[k <- v] m'.
Proof.
  intros H H'.
  rewrite /compatf catf_setr -H' -catf_setr.
  rewrite -{2}(catf0 m') -catf_setr -H.
  rewrite catfA catf_setr catf0 //.
Qed.

Hint Extern 1 (compatf11 ?m ?m') =>
  (by left) || (by right)
  : fmap_solve_db.

Hint Resolve compatf_set compatf_set_set compatfm0 compatf0m : fmap_solve_db.

Lemma catf_compat (m m' m'' : {fmap K → V})
  : compatf m m''
  → compatf m' m''
  → compatf (m + m') m''.
Proof.
  intros H H'.
  rewrite /compatf catfA -H -catfA H' catfA //.
Qed.

Lemma compatf_cat (m m' m'' : {fmap K → V})
  : compatf m m'
  → compatf m m''
  → compatf m (m' + m'').
Proof.
  intros H H'.
  rewrite /compatf catfA H -catfA H' catfA //.
Qed.

Hint Resolve catf_compat compatf_cat : fmap_solve_db.


Lemma submapf_set (k : K) (v : V) m m'
  : hasf m' k v
  → submapf m m'
  → submapf m.[k <- v] m'.
Proof.
  intros H H'.
  rewrite /submapf catf_setr H' H //.
Qed.

Hint Resolve sub0mapf subUmapf submapf_set : fmap_solve_db.


Lemma separatefUl (m m' : {fmap K → V}) (m'' : {fmap K → V'})
  : separatef m m'' → separatef m' m'' → separatef (m + m') m''.
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite domf_cat fdisjointUX H H' //.
Qed.

Lemma separatefUr (m : {fmap K → V}) (m' m'' : {fmap K → V'})
  : separatef m m' → separatef m m'' → separatef m (m' + m'').
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite domf_cat fdisjointXU H H' //.
Qed.

Lemma separatef_set_set (k k' : K) (v v' : V)
  (m : {fmap K → V}) (m' : {fmap K → V'})
  : separatef [fmap].[k <- v] m'
  → separatef m.[k' <- v'] m'
  → separatef m.[k' <- v'].[k <- v] m'.
Proof.
  intros [H] [H'].
  apply fsep.
  rewrite dom_setf fdisjointUX H'.
  rewrite dom_setf domf0 fsetU0 in H.
  rewrite H //.
Qed.

Lemma separatef_set (k k' : K) (v : V) (v' : V') (m' : {fmap K → V'})
  : k ≠ k'
  → separatef [fmap].[k <- v] m'
  → separatef [fmap].[k <- v] m'.[k' <- v'].
Proof.
  intros H [H'].
  apply fsep.
  rewrite dom_setf domf0 fsetU0 in H'.
  rewrite 2!dom_setf domf0 fsetU0 fdisjointXU H'.
  rewrite fdisjoint1X in_fset1.
  move: H => /eqP -> //.
Qed.

Lemma fseparate0m (m : {fmap K → V'})
  : @separatef K V V' [fmap] m.
Proof. apply fsep. rewrite domf0 fdisjoint0X //. Qed.

Lemma fseparatem0 (m : {fmap K → V})
  : @separatef K V V' m [fmap].
Proof. apply fsep. rewrite domf0 fdisjointX0 //. Qed.

Lemma fseparateE (m : {fmap K → V}) (m' : {fmap K → V'})
  : separatef m m' → [disjoint domf m & domf m'].
Proof. by intros [?]. Qed.


Lemma fseparateMl
  (f : V → V') (m : {fmap K → V}) (m' : {fmap K → V''})
  : separatef m m' → separatef (mapm m f) m'.
Proof. intros [H]. apply fsep. rewrite domm_map //. Qed.

Lemma fseparateMil {T : ordType} {S S' S'' : Type}
  (f : T → S → S') (m : {fmap T → S}) (m' : {fmap T → S''})
  : fseparate m m' → fseparate (mapim f m) m'.
Proof. intros [H]. apply fsep. rewrite domm_mapi //. Qed.

Lemma fseparateMr {T : ordType} {S S' S'' : Type}
  (f : S' → S'') (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → fseparate m (mapm f m').
Proof. intros [H]. apply fsep. rewrite domm_map //. Qed.

Lemma fseparateMir {T : ordType} {S S' S'' : Type}
  (f : T → S' → S'') (m : {fmap T → S}) (m' : {fmap T → S'})
  : fseparate m m' → fseparate m (mapim f m').
Proof. intros [H]. apply fsep. rewrite domm_mapi //. Qed.

Lemma notin_fseparate {T : ordType} {S S'} (x : T * S) (m : {fmap T → S'})
  : fseparate [fmap x] m → x.1 \notin domm m.
Proof.
  move=> [] /fdisjointP H.
  apply H.
  rewrite domm_set in_fsetU1 eq_refl //.
Qed.


Hint Extern 2 (?x ≠ ?y) =>
  done : fmap_solve_db.

Hint Resolve fseparateE fseparate0m fseparatem0 : fmap_solve_db.
Hint Resolve fseparateUl fseparateUr : fmap_solve_db.
Hint Resolve fseparateMl fseparateMr : fmap_solve_db.
Hint Resolve fseparateMil fseparateMir : fmap_solve_db.
Hint Resolve notin_fseparate fseparate_set fseparate_set1 : fmap_solve_db.


(* case over booleans *)

Lemma fsubmap_case_l {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fsubmap m m'' → fsubmap m' m'' → fsubmap (if b then m else m') m''.
Proof. by move: b => []. Qed.

Lemma fsubmap_case_r {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fsubmap m m' → fsubmap m m'' → fsubmap m (if b then m' else m'').
Proof. by move: b => []. Qed.

Lemma fcompat_case_l {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fcompat m m'' → fcompat m' m'' → fcompat (if b then m else m') m''.
Proof. by move: b => []. Qed.

Lemma fcompat_case_r {T : ordType} {S : Type} {b : bool} {m m' m'' : {fmap T → S}}
  : fcompat m m' → fcompat m m'' → fcompat m (if b then m' else m'').
Proof. by move: b => []. Qed.

Hint Resolve fsubmap_case_l fsubmap_case_r fcompat_case_l fcompat_case_r : fmap_solve_db.
