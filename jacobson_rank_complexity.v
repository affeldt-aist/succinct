From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import Omega Reals Rpower Fourier.
Require Import compact_data_structures rank_select.

(** * Space complexity of the rank algorithm *)

(** OUTLINE
  0. Section R_ext
     Section nat2ulst_ext.
  1. Section jacobson_rank_directories_storage.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Coercion INR : nat >-> R.
Coercion IZR : Z >-> R.

(* TODO: merge with inftheo/Rssr? *)
Section R_ext.

Definition floor (r : R) : Z := Int_part r.

Lemma Zlt1_floor (r : R) : 2 <= r -> (1 < floor r)%Z.
Proof.
move=> x1.
rewrite /floor.
case: (base_Int_part r) => H1 H2.
apply/lt_IZR; by fourier.
Qed.

Lemma Rle_floor (r : R) : (floor r <= r)%R.
Proof. by apply base_Int_part. Qed.

Lemma Zle0_floor (r : R) : (0 <= r)%R -> (0 <= floor r)%Z.
Proof.
rewrite /floor => r0.
case: (base_Int_part r) => _ H.
have {H}H : (Int_part r > -1)%R by fourier.
move: H; move/lt_IZR => H; omega.
Qed.

Lemma Zlt0_floor (r : R) : (1 <= r)%R -> (0 < floor r)%Z.
Proof.
move=> x1.
rewrite /floor.
case: (base_Int_part r) => H1 H2.
apply/lt_IZR; fourier.
Qed.

Lemma Rlt_floor r : (r < floor r + 1)%R.
Proof. case: (base_Int_part r) => _ ?; rewrite /floor; fourier. Qed.

Lemma Nat_pow_Rpower x : INR (expn 2 x) = Rpower 2 x.
Proof.
elim: x => [| x IH]; first by rewrite Rpower_O //; fourier.
rewrite expnS.
rewrite -(addn1 x) [in RHS]plus_INR Rpower_plus -IH Rpower_1; last by fourier.
by rewrite Rmult_comm mult_INR.
Qed.

End R_ext.

Definition log r := ln r / ln 2.
(* NB: from infotheo's log2.v *)
Axiom ln_2_neq0 : ln 2 <> 0.
Axiom log_1 : log 1 = 0.
Axiom log_2 : log 2 = 1.
Axiom log_increasing_le : forall a b, (0 < a -> a <= b -> log a <= log b)%R.
Axiom log_increasing : forall a b, (0 < a -> a < b -> log a < log b)%R.
Axiom log_mult : (forall x y, 0 < x -> 0 < y -> log (x * y) = log x + log y)%R.

Section nat2ulst_ext.

(* NB: from Seplog's listbit_correct.v *)
Axiom nat2ulst : nat -> seq bool.
Axiom nat2ulst_length : forall z m, (z < expn 2 m)%nat -> size (nat2ulst z) = m.

Definition bits_of_nats (s : seq nat) : seq bool := flatten [seq nat2ulst x | x <- s].

Lemma size_bits_of_nats M s :
  (forall x, x \in s -> size (nat2ulst x) = M) ->
  size (bits_of_nats s) = (size s * M)%nat.
Proof.
move=> H.
rewrite /bits_of_nats -sum1_size big_flatten /= big_map -sum1_size big_distrl /=.
rewrite (_ : s = filter (fun x => x \in s) s); last by rewrite -{1}(filter_predT s); apply eq_in_filter.
rewrite 2!big_filter.
apply eq_bigr => // i i_s.
by rewrite mul1n sum1_size H.
Qed.

Lemma size_nat2ulst_floor n M : (0 < M)%nat -> (n <= M)%nat ->
  (INR (size (nat2ulst n)) = floor (log M) + 1)%R.
Proof.
move=> Hs Hn.
rewrite INR_IZR_INZ.
set f := floor _.
have Hf : (0 <= f)%Z.
  apply/Zle0_floor/(Rle_trans _ (log M)); last by fourier.
  rewrite -log_1.
  apply log_increasing_le; first by fourier.
  rewrite (_ : 1%R = INR 1) //; by apply/le_INR/leP.
have -> : f = Z.of_nat (Z.abs_nat f) by rewrite Zabs2Nat.id_abs Z.abs_eq.
rewrite (_ : 1%R = Z.of_nat 1) //.
rewrite -plus_IZR.
rewrite -inj_plus.
congr Z.of_nat.
rewrite (@nat2ulst_length _ (Z.abs_nat f + 1)); last first.
  apply/ltP/INR_lt.
  apply (Rle_lt_trans _ (Rpower 2 (log M))).
    rewrite /Rpower /log /Rdiv Rmult_comm -Rmult_assoc Rinv_r_simpl_m; last exact ln_2_neq0.
    rewrite exp_ln //; by [apply/le_INR/leP | apply/lt_0_INR/ltP].
  rewrite (_ : INR (expn 2 _) = Rpower 2 (floor (log M) + 1)); last first.
    rewrite Nat_pow_Rpower INR_IZR_INZ // inj_plus Zabs2Nat.id_abs Z.abs_eq //.
    rewrite [in X in _ = Rpower _ X](_ : 1%R = Z.of_nat 1) //.
    by rewrite plus_IZR.
  apply Rpower_lt; first by fourier.
  exact: Rlt_floor.
by rewrite plusE.
Qed.

(* TODO: comes from infoteo's Rbigop *)
Canonical Structure mulR_muloid := Monoid.MulLaw Rmult_0_l Rmult_0_r.
Canonical Structure addR_monoid := Monoid.Law (fun a b c => sym_eq (Rplus_assoc a b c)) Rplus_0_l Rplus_0_r.
Canonical Structure addR_comoid := Monoid.ComLaw Rplus_comm.
Canonical Structure addR_addoid := Monoid.AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.
Canonical Rmult_monoid := Monoid.Law (fun a b c => sym_eq (Rmult_assoc a b c)) Rmult_1_l Rmult_1_r.
Canonical Structure mulR_comoid := Monoid.ComLaw Rmult_comm.

Lemma morph_plus_INR : {morph INR : x y / (x + y)%nat >-> (x + y)%R}.
Proof. move=> x y /=; by rewrite plus_INR. Qed.

Lemma size_bits_of_nats_for_R (M : R) s :
  (forall x, x \in s -> INR (size (nat2ulst x)) = M)%R ->
  (INR (size (bits_of_nats s)) = size s * M)%R.
Proof.
move=> H.
rewrite /bits_of_nats -sum1_size big_flatten /= big_map -sum1_size.
rewrite 2!(@big_morph R nat INR 0 Rplus O addn morph_plus_INR erefl) big_distrl /=.
rewrite (_ : s = filter (fun x => x \in s) s); last by rewrite -{1}(filter_predT s); apply eq_in_filter.
rewrite 2!big_filter.
apply eq_bigr => // i i_s.
rewrite Rmult_1_l sum1_size; by apply H.
Qed.

End nat2ulst_ext.

Section jacobson_rank_directories_storage.

Variables (T : eqType) (b : T).

Lemma storage_for_first_level_dir_entries sz1 (s : seq T) :
  (0 < size s)%nat ->
  forall e, e \in first_level_dir b sz1 s ->
  (INR (size (nat2ulst e)) = floor (log (size s)) + 1)%R.
Proof.
move=> s0 e /upper_bound_for_first_level_dir_entries es.
by apply: size_nat2ulst_floor => //.
Qed.

Lemma storage_for_first_level_dir s : (1 < size s)%nat ->
  let n := size s in
  let sz2 := floor (log n / 2) in
  let sz1 := Z.abs_nat (sz2 * floor (log n))%Z in
  (INR (size (bits_of_nats (first_level_dir b sz1 s))) = (floor (log n) + 1) * (n %/ sz1))%R.
Proof.
move=> Hs n sz2 sz1.
etransitivity.
  eapply size_bits_of_nats_for_R.
  apply storage_for_first_level_dir_entries.
  by rewrite (ltn_trans _ Hs).
by rewrite /first_level_dir size_map size_iota -/n Rmult_comm.
Qed.

Lemma storage_for_second_level_dir_head_entries k' sz2 (s : seq T) :
  (0 < sz2)%nat ->
  let sz1 := (k'.+1 * sz2)%nat in
  forall n, n \in flatten (second_level_dir_head b sz2 k'.+1 s) ->
  (INR (size (nat2ulst n)) = floor (log sz1) + 1)%R.
Proof.
move=> Hsz2 sz1 n /upper_bound_for_second_level_dir_head_entries Hn.
by rewrite (size_nat2ulst_floor _ Hn) // ltn_addr.
Qed.

Lemma storage_for_second_level_dir s : (3 < size s)%nat ->
  let n := size s in
  let sz2 := Z.abs_nat (floor (log n / 2))  in
  let k := Z.abs_nat (floor (log n)) (* number of small blocks in a big block *) in
  let sz1 := (k * sz2)%nat in
  (INR (size (bits_of_nats (flatten (second_level_dir_head b sz2 k s)))) =
    ((floor (log sz1) + 1) * (n %/ sz1 * k.-1))%R).
Proof.
move=> Hs n sz2 k sz1.
have k0 : (0 < k)%nat.
  rewrite /k.
  rewrite (_ : O = Z.abs_nat 0) //.
  apply/ltP/Zabs_nat_lt; split => //.
  apply Zlt0_floor.
  rewrite -log_2.
  apply log_increasing_le; first by fourier.
  rewrite (_ : 2%R = INR 2) //.
  apply/le_INR/leP.
  by apply: ltn_trans Hs.
have logn2 : (2 <= log n)%R.
  rewrite (_ : 2%R = log (2 * 2)); last first.
    rewrite log_mult.
    by rewrite log_2.
    by fourier.
    by fourier.
  apply log_increasing_le; first by fourier.
  rewrite (_ : 2 * 2 = INR 4)%R.
  by apply/le_INR/leP.
  rewrite /INR; field.
have sz20 : (0 < sz2)%nat.
  rewrite /sz2 /k (_ : O = Z.abs_nat 0) //.
  apply/ltP/Zabs_nat_lt; split => //.
  apply Zlt0_floor; fourier.
have k_pred : k.-1.+1 = k by rewrite prednK.
rewrite (@size_bits_of_nats_for_R (floor (log sz1) + 1)); last first.
  move=> x /= Hx.
  rewrite -k_pred in Hx.
  rewrite (storage_for_second_level_dir_head_entries sz20 Hx) //.
  by rewrite prednK //.
rewrite -k_pred.
rewrite size_flatten_second_level_dir_head //.
rewrite /= prednK // -/sz1 -/n.
by rewrite mult_INR Rmult_comm.
Qed.

End jacobson_rank_directories_storage.

(* TODO: the same using fixed-size integers? *)
Inductive int n : Type := mk_int (lst : list bool) of size lst = n.
Definition zext m l := nseq m false ++ l.
Definition adjust_u l n := if (size l < n)%nat then
                             zext (n - size l) l
                           else
                             drop (size l - n) l.
Axiom Z2u : forall n (z : Z), int n.
Axiom len_adjust_u : forall n l, size (adjust_u l n) = n.
Axiom bits_of_int : forall n, int n -> seq bool.
Axiom size_bits_of_int : forall n (a : int n), size (bits_of_int a) = n.
Axiom ulst2nat : seq bool -> nat.
Definition u2Zc := fun n (a : int n) => match a with mk_int lst _ => ulst2nat lst end.
Axiom adjust_ulst2nat: forall n lst, ulst2nat lst < 2 ^ n -> ulst2nat (adjust_u lst n) = ulst2nat lst.
Axiom nat2ulstK : forall n, (0 <= n)%nat -> ulst2nat (nat2ulst n) = n.

Definition first_level_dir' (sz : nat) (s : seq bool) : seq (int (Z.abs_nat (floor (log (size s)))).+1).
pose number_of_blocks := size s %/ sz.
refine ([seq _ s | x <- iota 1 number_of_blocks]).
intro s'.
apply mk_int with (adjust_u (nat2ulst (rank true (x * sz) s')) (Z.abs_nat (floor (log (size s)))).+1).
apply len_adjust_u.
Defined.
