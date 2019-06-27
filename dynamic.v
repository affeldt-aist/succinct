From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import tree_traversal rank_select insert_delete Program.
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

(* due to technical reason, to generate OCaml code in dynamic_dependent_tactic.v *)
Inductive tree_ml : Type :=
| LeafML : forall(arr : seq bool), tree_ml
| NodeML : forall(s1 s2 o1 o2 : nat) (c : color) (l r : tree_ml), tree_ml.
(*                         *)

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

Lemma size_of_tree_pos num ones d c (B : tree num ones d c) :
  size_of_tree B > 0.
Proof.
elim: B => //= lnum lones rnum rones d' cl cr c' ok_l ok_r l IHl r IHr.
by rewrite addn_gt0 IHl orTb.
Qed.

Fixpoint dflatten {n m d c} (B : tree n m d c) :=
  match B with
  | Node _ _ _ _ _ _ _ _ _ _ l r => dflatten l ++ dflatten r
  | Leaf s _ _ => s
  end.

Lemma size_dflatten {n m d c} (B : tree n m d c) : size (dflatten B) = n.
Proof.
elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
by rewrite size_cat IHl IHr.
Qed.

Lemma count_one_dflatten {n m d c} (B : tree n m d c) : count_one (dflatten B) = m.
Proof.
elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
rewrite /count_one in IHl,IHr.
by rewrite /count_one count_cat IHl IHr.
Qed.

Definition rnode {s1 s2 o1 o2 d} (l : tree s1 o1 d Black)
  (r : tree s2 o2 d Black) : tree (s1 + s2) (o1 + o2) d Red :=
  Node red_black_ok red_black_ok l r.

Definition bnode {s1 s2 o1 o2 d cl cr} (l : tree s1 o1 d cl)
  (r : tree s2 o2 d cr) : tree (s1 + s2) (o1 + o2) (incr_black d Black) Black :=
  Node (black_any_ok cl) (black_any_ok cr) l r.

Inductive near_tree : nat -> nat -> nat -> color -> Type :=
| Bad : forall {s1 o1 s2 o2 s3 o3 d},
    tree s1 o1 d Black ->
    tree s2 o2 d Black ->
    tree s3 o3 d Black ->
    near_tree (s1 + s2 + s3) (o1 + o2 + o3) d Red
| Good: forall {s o d c} p,
    tree s o d c ->
    near_tree s o d p.

Definition fix_color {nl ml d c} (l : near_tree nl ml d c) :=
  match l with
  | Bad _ _ _ _ _ _ _ _ _ _ => Red
  | Good _ _ _ _ _ _ => Black
  end.

Definition black_of_bad {nl ml d c} (l : near_tree nl ml d c) :=
  match l with
  | Bad _ _ _ _ _ _ _ _ _ _ => Black
  | Good _ _ _ c _ _ => c
  end.

Definition fix_near_tree {num ones d c} (t : near_tree num ones d c) :
  tree num ones (incr_black d (inv (fix_color t))) (black_of_bad t) :=
  match t with
  | Bad _ _ _ _ _ _ _ t1 t2 t3 => bnode (rnode t1 t2) t3
  | Good _ _ _ _ _ t' => t'
  end.

Definition dflatteni {num ones d c} (B : near_tree num ones d c) :=
  match B with
  | Bad _ _ _ _ _ _ _ t1 t2 t3 => dflatten t1 ++ dflatten t2 ++ dflatten t3
  | Good _ _ _ _ _ t' => dflatten t'
  end.

Lemma fix_near_treeK {num ones d c} (t : near_tree num ones d c) :
  dflatten (fix_near_tree t) = dflatteni t.
Proof.
case: t => //= num1 ones1 num2 ones2 num3 ones3 d' t1 t2 t3;  by rewrite catA.
Qed.

Lemma dflatten_ones {num ones d c} (B : tree num ones d c) :
  ones = count_mem true (dflatten B).
Proof.
elim: B => //= s1 o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr.
by rewrite count_cat -IHl -IHr.
Qed.

Lemma ones_lt_num num ones d c (B : tree num ones d c) :
  ones <= num.
Proof.
  by rewrite (dflatten_ones B) -[in X in _ <= X](size_dflatten B) count_size.
Qed.

Lemma dflatten_zeroes num ones d c (B : tree num ones d c) :
  num - ones = count_mem false (dflatten B).
Proof.
  rewrite [in LHS](dflatten_ones B) -[in X in X - _](size_dflatten B).
  apply/eqP. rewrite -(eqn_add2r (count_mem true (dflatten B))) subnK.
    by rewrite -(count_predC (pred1 false)) eqn_add2l; apply/eqP/eq_count; case.
  by rewrite -(dflatten_ones B) (size_dflatten B)(ones_lt_num B).
Qed.

Lemma dflatten_rank num ones d c (B : tree num ones d c) :
  ones = rank true num (dflatten B).
Proof.
by rewrite /rank -[X in take X _](size_dflatten B) take_size -dflatten_ones.
Qed.

End wordsize.
