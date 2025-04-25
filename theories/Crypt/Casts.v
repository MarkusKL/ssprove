Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrbool ssrnat choice fintype eqtype all_algebra finmap.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Coq Require Import ZArith.
From SSProve.Crypt Require Import Prelude.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_util.


From HB Require Import structures.

(**
  Note for any of these types it would also be okay to write the cast, e.g., [(nat:choiceType)%type],
  directly in the term.
  This (backward-compatibility) file just made porting to mathcomp 2.1.0 easier.
  Just delete as soon as all references to the below casts are gone from the code base.
 *)

Definition unit_choiceType : choiceType := Datatypes.unit.
Definition nat_choiceType : choiceType := nat.
Definition int_choiceType : choiceType := Z.
Definition bool_choiceType : choiceType := bool.
Definition prod_choiceType (A B: choiceType) : choiceType := prod A B.
Definition fmap_choiceType (A B: choiceType) : choiceType := {fmap A -> B}.
Definition option_choiceType (A: choiceType) : choiceType := option A.
Definition fin_choiceType (p: positive) : choiceType := ordinal p.(pos).
Definition word_choiceType (nbits : wsize) : choiceType := word nbits.
Definition list_choiceType (A : choiceType) : choiceType := list A.
Definition sum_choiceType (A B: choiceType) : choiceType := (A + B)%type.

Definition prod_finType (A B: finType) : finType := prod A B.
