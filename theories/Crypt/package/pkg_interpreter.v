Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".
Require Arith ZArith.

From SSProve.Crypt Require Import Prelude choice_type
     pkg_core_definition pkg_tactics pkg_distr pkg_notation.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

(* From Jasmin Require Import word. *)
From SSProve.Crypt Require Import jasmin_word.

From Equations Require Import Equations.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Interpreter.
  Import PackageNotation.
  #[local] Open Scope package_scope.

  Context (sample : ∀ (e : choice_type), nat → option (nat * e)).

  Definition NatState := nat.

  Definition nat_ch (x : option NatState) (l : choice_type) : option l :=
    match x with
    | Some v => unpickle v
    | None => None
    end.

  Definition ch_nat (l : choice_type) (v : l) : option NatState :=
    Some (pickle v).

  Definition new_state
             (st : Location → option NatState) (l : Location) (v : l) : (Location → option NatState)
    :=
    fun (l' : Location) =>
      if l.1 == l'.1
      then (ch_nat l v)
      else st l'.

  Fixpoint Run_aux {A : choiceType}
           (c : raw_code A) (seed : nat) (st : Location → option NatState)
    : option A :=
    match c with
      ret x => Some x
    | sampler o k =>
        match sample (projT1 o) seed with
        | Some (seed', x) => Run_aux (k x) seed' st
        | _ => None
        end
    | opr o x k => None (* Calls should be inlined before we can run the program *)
    | putr l v k => Run_aux k seed (new_state st l v)
    | getr l k =>
        match nat_ch (st l) l with
          | Some v => Run_aux (k v) seed st
          | None => None
        end
    end.

  Definition Run {A} :=
    (fun c seed => @Run_aux A c seed (fun (l : Location) => Some 0)).

  #[program] Fixpoint sampler (e : choice_type) seed : option (nat * e):=
    match e with
    | chUnit => Some (seed, Datatypes.tt)
    | chNat => Some ((seed + 1)%nat, seed)
    | chInt => Some ((seed + 1)%nat, BinInt.Z.of_nat seed) (* FIXME: also generate negative numbers *)
    | chBool => Some ((seed + 1)%nat, Nat.even seed)
    | chProd A B =>
        match sampler A seed with
        | Some (seed' , x) => match sampler B seed' with
                              | Some (seed'', y) => Some (seed'', (x, y))
                              | _ => None
                              end
        | _ => None
        end
    | chMap A B => None
    | chOption A =>
        match sampler A seed with
        | Some (seed', x) => Some (seed', Some x)
        | _ => None
        end
    | chFin n => Some ((seed + 1)%N, _)
    | chWord n => Some ((seed + 1)%N, _)
    | chList A =>
        match sampler A seed with
        | Some (seed', x) => Some (seed', [:: x])
        | _ => None
        end
    | chSum A B =>
        let '(seed', b) := ((seed + 1)%nat, Nat.even seed) in
        if b
        then
          match sampler A seed' with
          | Some (seed'' , x) => Some (seed'', inl x)
          | _ => None
          end
        else
          match sampler B seed' with
          | Some (seed'' , y) => Some (seed'', inr y)
          | _ => None
          end
    end.
  Next Obligation.
    eapply Ordinal.
    instantiate (1 := (seed %% n)%N).
    rewrite ltn_mod.
    apply n.
  Defined.

  Set Warnings "-notation-overridden,-ambiguous-paths".
  Import ZArith.
  Import all_algebra.
  Set Warnings "notation-overridden,ambiguous-paths".
  Local Open Scope Z_scope.
  Local Open Scope ring_scope.

  Next Obligation.
    eapply word.mkWord.
    instantiate (1 := ((Z.of_nat seed) mod (word.modulus (nat_of_wsize n) ))%Z).
    pose (Z.mod_bound_pos (Z.of_nat seed) (word.modulus n)
         (Zle_0_nat seed)).
    pose (word.modulus_gt0 (nat_of_wsize n)).
    apply / word.iswordZP.
    apply a.
    move : i => / word_ssrZ.ltzP.
    auto.
  Defined.

End Interpreter.
