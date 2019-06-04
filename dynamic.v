From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program.
Require Import set_clear Compare_dec ExtrOcamlNatInt.

Set Implicit Arguments.

Section color.

Inductive color := Red | Black.

Definition color_ok parent child : bool :=
  match parent,child with
  | Red, Red => false
  | _,_ => true
  end.

Definition eq_color c1 c2 :=
  match c1,c2 with
  | Black,Black | Red,Red => true
  | _,_ => false
  end.

Lemma color_eqP : Equality.axiom eq_color.
Proof.
  move; case; case => /=;
  try apply ReflectT => //;
  apply ReflectF => //.
Qed.

Canonical color_eqMixin := EqMixin color_eqP.
Canonical color_eqType := Eval hnf in EqType color color_eqMixin.

Definition incr_black d c :=
  match c with
  | Black => d.+1
  | Red => d
  end.

Lemma incr_black_prop d c : incr_black d c = d + (c == Black).
Proof. case: c => //=; by rewrite ?(addn0,addn1). Qed.

Definition inv c := if c is Black then Red else Black.

Definition red_black_ok : color_ok Red Black := erefl.

Definition black_any_ok c : color_ok Black c := erefl.

End color.

Section wordsize.

Variable w : nat.
Hypothesis wordsize_gt1: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. exact/ltnW/wordsize_gt1. Qed.

Lemma wordsize_neq0 : w != 0.
Proof. rewrite -lt0n; exact wordsize_gt0. Qed.

Lemma wordsize_sqrn_gt0 : w ^ 2 > 0.
Proof. by rewrite sqrn_gt0 lt0n wordsize_neq0. Qed.

Lemma wordsize_sqrn_gt2 : w ^ 2 > 2.
Proof. by move: wordsize_gt1; case: w => // -[//|] []. Qed.

Lemma wordsize_sqrn_div2_neq0 : w ^ 2 %/ 2 <> 0.
Proof.
by move/eqP; rewrite gtn_eqF // divn_gt0 // (ltn_trans _ wordsize_sqrn_gt2).
Qed.

(* work around for program fixpoint *)
(*Definition count_one arr := count_mem true arr.*)

Inductive tree : nat -> nat -> nat -> color -> Type :=
| Leaf : forall (arr : seq bool),
    (w ^ 2) %/ 2 <= size arr ->
    2 * (w ^ 2) > size arr ->
    tree (size arr) (count_one arr) 0 Black
| Node : forall {s1 o1 s2 o2 d cl cr c},
    color_ok c cl -> color_ok c cr ->
    tree s1 o1 d cl -> tree s2 o2 d cr ->
    tree (s1 + s2) (o1 + o2) (incr_black d c) c.

Fixpoint size_of_tree {s o d c} (t : tree s o d c) : nat :=
  match t with
  | Leaf _ _ _ => 1
  | Node _ _ _ _ _ _ _ _ _ _ l r => size_of_tree l + size_of_tree r
  end.

End wordsize.
