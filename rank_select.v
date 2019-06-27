From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import tree_traversal.

(** A formalization of the rank and select functions *)

(** OUTLINE
  0. Section incremental
  1. Section rank_def
  2. Section rank_prop
  3. Section binary_rank
  4. Section select_def
  5. Section select_prop
  6. Module rank_select_test
  7. Section jacobson_rank_directories.
       Section first_level_dir
       Section second_level_dir
       Section storage_dir
  8. Section jacobson_rank_algorithm.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section incremental.

Variable f : nat -> nat.

Definition incremental f := forall n, (f n.+1 == f n) || (f n.+1 == (f n).+1).

Lemma incremental_rev :
  incremental f ->
  forall m n x, m <= n -> f m <= x <= f n ->
                exists i, (m <= i <= n) && (f i == x).
Proof.
move=> Hf m n x.
elim: n => [|n IH] /=.
  rewrite leqn0 => /eqP ->.
  rewrite -eqn_leq => /eqP <-.
  by exists 0; rewrite eqxx.
case Hfn: (f n.+1 == x).
  rewrite -(eqP Hfn) => Hm Hfm.
  by exists n.+1; rewrite Hm leqnn eqxx.
rewrite leq_eqVlt => /orP [/eqP ->|].
  rewrite -eqn_leq => Hfn'.
  by rewrite Hfn' in Hfn.
rewrite ltnS.
move=> Hm Hfm.
suff : exists i : nat, (m <= i <= n) && (f i == x).
  move=> [i] /andP [/andP [Hi Hi'] Hfi].
  by exists i; rewrite Hi Hfi (leq_trans Hi').
apply IH => //.
move/orP: (Hf n) Hfn Hfm => [] /eqP -> // Hfn.
by rewrite (leq_eqVlt x) eq_sym Hfn ltnS.
Qed.

Lemma incr_shift_x m n (x : 'I_((f n).+1 - f m)) : f m <= f m + x <= f n.
case: x => x Hx; rewrite leq_addr /= -ltnS -ltn_subRL; exact.
Qed.

Definition incremental_inv Hf m n (Hmn : m <= n) :=
   fun x : 'I_((f n).+1 - f m) =>
     ex_minn (incremental_rev Hf (x := f m + x) Hmn (incr_shift_x x)).

End incremental.

Section rank_def.

Variables (T : eqType) (b : T) (n : nat).

(* wikipedia def *)
Definition Rank (i : nat) (B : n.-tuple T) :=
  #| [set k : [1,n] | (k <= i) && (tacc B k == b)] |.

End rank_def.

Section rank_prop.

Variables (T : eqType).
Implicit Types s : seq T.

Lemma Rank_ub n (b : T) (i : nat) (B : n.-tuple T) : Rank b i B <= n.
Proof.
by rewrite /Rank (leq_trans (max_card _)) // leq_eqVlt card_idx eqxx.
Qed.

(* naive definition of rank *)
Definition rank b i s := count_mem b (take i s).

Lemma RankE n b i (B : n.-tuple T) : Rank b i B = rank b i B.
Proof.
rewrite /Rank cardE size_filter.
transitivity (count (mem [set k | tnth B k == b]) [seq k : 'I_n <- enum 'I_n | k < i]).
  rewrite enumT count_filter.
  rewrite (_ : (Finite.enum (ordinal_finType n)) = map (@ord_of n) (map (@of_ord n) (Finite.enum (ordinal_finType n)))); last first.
    by rewrite -map_comp map_id_in //= => j _; rewrite of_ordK.
  rewrite count_map.
  rewrite (_ : [seq (@of_ord n) i | i <- Finite.enum (ordinal_finType n)] = (Finite.enum (idx_finType n))); last first.
    by rewrite of_ord_enum.
  apply eq_count => k.
  rewrite !inE andbC.
  congr andb.
  rewrite /ord_of ffunE /=.
  by rewrite prednK.
rewrite -(map_tnth_enum B) /rank -map_take count_map.
suff -> : [seq k : 'I_n <- enum 'I_n | k < i] = take i (enum 'I_n).
  apply eq_count => k; by rewrite !inE.
rewrite -{1}(cat_take_drop i (enum _)) filter_cat -(@eq_in_filter _ predT); last first.
  move=> j /(map_f val).
  rewrite map_take val_enum_ord.
  case: (ltnP i n) => [ni|ni _].
    rewrite -[X in iota _ X](subnKC (ltnW ni)) iota_add add0n take_cat.
    by rewrite size_iota ltnn subnn take0 cats0 mem_iota add0n leq0n /= => ->.
  by rewrite (@leq_trans n).
rewrite filter_predT -(@eq_in_filter _ pred0); last first.
  move=> /= j /(map_f val).
  rewrite map_drop val_enum_ord.
  case: (ltnP i n) => ni.
    rewrite -[X in iota _ X](subnKC (ltnW ni)) iota_add.
    rewrite add0n drop_cat size_iota ltnn subnn drop0 mem_iota leqNgt.
    by case/andP => /negbTE => ->.
  by rewrite drop_oversize // size_iota.
by rewrite filter_pred0 cats0.
Qed.

Lemma rankE b i (B : seq T) : rank b i B = Rank b i (in_tuple B).
Proof. by rewrite RankE. Qed.

Lemma rank0 b s : rank b 0 s = 0.
Proof. by rewrite /rank take0. Qed.

Lemma rank_nil b i : rank b i [::] = 0.
Proof. by rewrite /rank take_oversize. Qed.

Lemma rank_cons b i h t : rank b i.+1 (h :: t) = (h == b) + rank b i t.
Proof. by case: t. Qed.

Lemma rank_leq b i s : rank b i s <= i.
Proof.
elim: s i => // h t IH [ // | i].
by rewrite rank_cons -addn1 addnC leq_add // leq_b1.
Qed.

Lemma leq_rank_count b i s : rank b i s <= count_mem b s.
Proof. by rewrite -{2}(cat_take_drop i s) count_cat leq_addr. Qed.

Lemma rank_incr b s i j (ij : i <= j) : rank b i s <= rank b j s.
Proof.
rewrite /rank; case: (leqP (size s) i) => H.
  by rewrite take_oversize // take_oversize // (leq_trans H).
case: (leqP (size s) j) => H1.
  by rewrite (take_oversize H1) -{2}(cat_take_drop i s) count_cat leq_addr.
rewrite -{2}(cat_take_drop i s) take_cat size_take H ltnNge ij /=.
by rewrite count_cat leq_addr.
Qed.

Lemma rank_cat b i s t : rank b i (s ++ t) =
  if i < size s then rank b i s else rank b (size s) s + rank b (i - size s) t.
Proof.
rewrite /rank take_cat; case: ifP => // /negbT.
rewrite -leqNgt => s1i; by rewrite count_cat (@take_oversize _ _ s).
Qed.

Lemma rank_over b i s : size s <= i -> rank b i s = rank b (size s) s.
Proof.
elim: s i => // h t IH [|i] //=.
rewrite ltnS => ti; by rewrite /rank /= !take_oversize.
Qed.

Lemma rank_addn b i j s : rank b (i + j) s = rank b i s + rank b j (drop i s).
Proof.
rewrite [in RHS]/rank -count_cat; congr count.
elim: i s => [?|i IH [//|h t]]; first by rewrite take0 drop0.
by rewrite addSn !take_cons IH.
Qed.

Lemma rank_take b s i j : i <= j -> rank b i (take j s) = rank b i s.
Proof. by move=> ij; rewrite /rank take_take. Qed.

Lemma rank_incremental b s : incremental (fun k => rank b k s).
Proof.
elim: s => //= a s IH [|m]; rewrite !rank_cons.
  rewrite !rank0; by case (a == b).
by rewrite -addnS !eqn_add2l.
Qed.

Lemma rank_exists b i s :
  i <= count_mem b s -> exists k, k <= size s /\ rank b k s = i.
Proof.
move=> Hi.
move: (@incremental_rev _ (rank_incremental b s) 0 (size s) i).
rewrite rank0 !leq0n {1}/rank /= take_size => /(_ erefl Hi) [k] /andP [Hk Hrk].
by exists k; rewrite Hk (eqP Hrk).
Qed.

Lemma rank_exists_lt b i s :
  i < count_mem b s -> exists k, k < size s /\ rank b k s = i.
Proof.
move=> Hi.
have [k []] := rank_exists (ltnW Hi).
rewrite leq_eqVlt => /orP [/eqP ->|].
  rewrite /rank take_size => Hi'; by rewrite Hi' ltnn in Hi.
move=> Hk Hrk; by exists k.
Qed.

Lemma rank_size sz b s : sz = size s -> rank b sz s = count_mem b s.
Proof. by move=> ->; rewrite /rank take_oversize. Qed.

Lemma rank_not_enough b (s : seq T) i : count_mem b s < i -> forall k, rank b k s < i.
Proof.
move=> Hi k.
rewrite /rank (leq_ltn_trans _ Hi) // -!sum1_count.
by rewrite -{2}(cat_take_drop k s) big_cat /= leq_addr.
Qed.

Lemma rank_same_nseq (b : T) n s :
  rank b n s = n -> take n s = nseq n b.
Proof.
rewrite/rank => Hcnt.
move: (count_size (pred1 b) (take n s)) (all_count (pred1 b) (take n s)).
rewrite Hcnt => Hs.
have Hn: n <= size s.
  apply (leq_trans Hs).
  rewrite size_take.
  case: ifP => //.
  by apply ltnW.
rewrite size_takel //.
rewrite eqxx => /all_pred1P -> //.
by rewrite size_takel.
Qed.

End rank_prop.
Arguments rank_size [_] _.

Section binary_rank.

Let brank := @rank bool_eqType.

Lemma brank_negbE (s : bitseq) (b : bool) (i : nat) : i <= size s ->
  brank b i s = i - brank (negb b) i s.
Proof.
move=> si; apply/eqP.
rewrite -(eqn_add2r (brank (~~ b) i s)) subnK ?rank_leq //.
have /eq_count : pred1 (~~ b) =1 predC (pred1 b) by case: b; case.
rewrite /brank /rank => ->; rewrite count_predC size_take.
by case: ifPn => //; rewrite -leqNgt eqn_leq si => ->.
Qed.

Lemma brank_sum_take (s : bitseq) i : brank true i s = \sum_(j <- take i s) j.
Proof.
elim: s i => [i|h t IH [|i]]; rewrite /brank ?(rank_nil,rank0,take0,big_nil) //.
rewrite rank_cons take_cons big_cons -IH; by case: h.
Qed.

Lemma brank_sum_nth (s : bitseq) i : brank true i s = \sum_(j < i) nth false s j.
Proof.
elim : s i => [i| h t IH [|i]]; rewrite /brank.
  rewrite rank_nil (eq_bigr (fun=> 0)) ?big_const ?iter_addn //=.
  move=> *; by rewrite nth_nil.
  by rewrite rank0 big_ord0.
rewrite rank_cons big_ord_recl /= -IH; by case: h.
Qed.

(* The b = true case is a corollary of brank_sum_nth *)
Lemma nth_brank1 b n B : nth (negb b) B n = b -> brank b 1 (drop n B) = 1.
Proof.
elim: n B b => [|n IH] [[] //|a B] /= b Hn.
+ by rewrite Hn /brank rank_cons rank0 eqxx.
+ by rewrite IH.
Qed.

End binary_rank.

Section select_def.

Variables (T : eqType) (b : T) (n : nat).

Lemma select_spec (i : nat) (B : n.-tuple T) :
  exists k, ((k <= n) && (Rank b k B == i)) || (k == n.+1) && (count_mem b B < i).
Proof.
case: (leqP i (count_mem b B)) => [Hi | /rank_not_enough H].
  have [k [Hk Hrk]] := rank_exists Hi.
  by exists k; rewrite -{1}(size_tuple B) Hk RankE Hrk eqxx.
by exists n.+1; rewrite eqxx orbT.
Qed.

Definition Select i (B : n.-tuple T) := ex_minn (select_spec i B).

Lemma Select0 (B : n.-tuple T) : Select O B = O.
Proof.
rewrite /Select; case: ex_minnP => m; rewrite ltn0 andbF orbF => H /(_ O).
by rewrite leq0n RankE /= rank0 eqxx leqn0 => /(_ isT)/eqP.
Qed.

End select_def.

Section select_prop.

Variables (T : eqType) (b : T).

Lemma SelectK n (s : n.-tuple T) (j : nat) :
  j <= count_mem b s -> Rank b (Select b j s) s = j.
Proof.
move=> js.
rewrite /Select; case: ex_minnP => m.
case/orP => [/andP[mn /eqP mj _]//|].
by rewrite ltnNge js andbF.
Qed.

Fixpoint select i (s : seq T) : nat :=
  if i is i.+1 then
     if s is a :: s' then
       (if a == b then select i s' else select i.+1 s').+1
     else 1
  else 0.

Lemma select0 s : select 0 s = 0.
Proof. by case: s. Qed.

Lemma select_nil i : select i [::] = (i != O).
Proof. rewrite /select; by case: i. Qed.

Lemma select_over i s : i > count_mem b s -> select i s = (size s).+1.
Proof.
elim: s i => [?|h t IH]; first by rewrite lt0n select_nil => ->.
case=> //= i; rewrite ltnS.
case: ifPn => [/eqP ?| hb Hi]; by [rewrite add1n => /IH -> | rewrite IH].
Qed.

Lemma select_index i s : i <= (count_mem b) s ->
  select i s = index i (mkseq ((rank b)^~ s) (size s)).
Proof.
elim: s i => [i|a s IH [//|/= i Hi]] /=; first by rewrite leqn0; case: i.
rewrite -(addn0 1) iota_addl -map_comp; congr S.
case: ifP Hi => //= ab.
- rewrite add1n ltnS => Hi.
  rewrite IH // -[LHS](index_map succn_inj) -map_comp; congr index.
  apply eq_map => j /=; by rewrite add1n rank_cons ab add1n.
- rewrite add0n => Hi; rewrite IH //; congr index.
  apply eq_map => j /=; by rewrite add1n rank_cons ab.
Qed.

Lemma select_ub s i : i <= (count_mem b) s -> select i s <= size s.
Proof.
move/select_index => ->.
by rewrite (leq_trans (index_size _ _)) // size_map size_iota.
Qed.

Lemma SelectE i n (s : n.-tuple T) : Select b i s = select i s.
Proof.
rewrite /Select.
case: ex_minnP => m /orP[/andP[mn H] Hmin|/andP[/eqP nm si] H].
- have /select_index -> : i <= (count_mem b) s.
    by rewrite -(eqP H) RankE leq_rank_count.
  rewrite /mkseq size_tuple -{2}(subnKC mn) iota_add map_cat add0n index_cat.
  case: ifP => [ /mapP[x] | _].
  + rewrite mem_iota leq0n add0n andTb => xm xi.
    move: (Hmin x).
    rewrite RankE xi (leq_trans (ltnW xm) mn) /= eqxx /= => /(_ isT).
    by move/(leq_trans xm); rewrite ltnn.
  + rewrite size_map size_iota (_ : index _ _ = 0) ?addn0 //.
    move: mn; rewrite leq_eqVlt => /orP[/eqP ->|mn]; first by rewrite subnn.
    destruct n as [|n'] => //; by rewrite subSn //= -RankE H.
- by rewrite select_over // size_tuple nm.
Qed.

Lemma selectE i (s : seq T) : select i s = Select b i (in_tuple s).
Proof. by rewrite SelectE. Qed.

Lemma selectK (s : seq T) (j : nat) : j <= count_mem b s ->
  rank b (select j s) s = j.
Proof. by move=> js; rewrite rankE selectE SelectK. Qed.

Lemma select_incr (s : seq T) i j (ij : i <= j) : select i s <= select j s.
Proof.
elim: s i j ij => [i j ij|s1 s2 H].
  rewrite !select_nil; by move: i j ij => -[//|i] [].
move=> -[//|i] [//|j]; rewrite ltnS => ij /=.
case: ifPn => ?; by rewrite ltnS H.
Qed.

Lemma select_cons_eq i t : select i.+1 (b :: t) = (select i t).+1.
Proof. by rewrite /= eqxx. Qed.

Lemma select_cons_neq i h t : h != b -> select i.+1 (h :: t) = (select i.+1 t).+1.
Proof. by move=> hb; rewrite /= (negbTE hb). Qed.

(*
NB(rei): moved to pred_succ.v because the lhs is pred,
the name RankK is a bit misleading, and pred_succ.v lacks lemmas
Theorem RankK n (s : n.-tuple T) j :
  rank b 1 (drop j s) = 1 -> Select b (Rank b j.+1 s) s = j.+1.
Proof.
destruct s as [s Hs] => /= Hrk.
rewrite SelectE RankE /=.
rewrite -(addn1 j) rank_addn.
rewrite Hrk addn1.
elim: j s {Hs} Hrk => [|j IH] [|a s] //=; rewrite rank_cons.
  case: (a == b); by rewrite !rank0 addn0 // select0.
case: (a == b) => /= Hrk; by rewrite ?add0n IH.
Qed.*)

Lemma select_cat i s t :
  select i (s ++ t) =
  if i <= count_mem b s then select i s
  else size s + select (i - count_mem b s) t.
Proof.
elim: s i => [|a s IH] [|i] //=.
  by rewrite select0.
case: ifP => Ha /=.
  rewrite IH ltnS; by case: ifP.
rewrite addSn add0n IH; by case: ifP.
Qed.

Lemma select_cat_ge i s t :
  select i s >= size s ->
  select i (s ++ t) = size s + select (i - count_mem b s) t.
Proof.
rewrite select_cat.
case: ifP => // Hi; move: (Hi); rewrite -subn_eq0 => /eqP ->.
rewrite select0 addn0 leq_eqVlt => /orP[/eqP //|].
by rewrite ltnNge (select_ub Hi).
Qed.

Lemma select_addn i j s :
  select (i + j) s =
  if i <= count_mem b s then
    select i s + select j (drop (select i s) s)
  else (size s).+1.
Proof.
elim: s i => //= [|a s IH] [|i] //.
rewrite addSn.
case: ifP => Ha.
  rewrite IH ltnS; by case: ifP.
rewrite /= add0n -addSn IH; by case: ifP.
Qed.

Lemma select_strict i j B :
  select i B < select j B -> i < j.
Proof.
elim: B i j => [|a B IH] [|i] [|j] //=.
by case: ifP => Ha; rewrite ltnS => /IH.
Qed.

Lemma leq_select_size i B :
  select i B <= size B + (count_mem b B < i).
Proof.
elim: B i => [|a B IH] [|i] //=.
case: (a == b); by apply (leq_trans (IH _)).
Qed.

Lemma select_count m l :
  select m l = size l -> count_mem b l = m.
Proof. elim: l m => [|a l IH] /= [|m] //. by case: ifP => _ [] /IH ->. Qed.

Lemma select_all_same n s :
  take n s = nseq n b -> select n s = n.
Proof. elim: n s => [|n IH] [|a s] //= [] -> Ht; by rewrite eqxx IH. Qed.

(* O(log n) implementation using binary search *)
Definition select_binarysearch (i : nat) (s : seq T) : nat :=
  binarysearch i (fun p => rank b p s) (size s).+1 (O, (size s)).

Lemma select_binarysearchE (n i : nat) (s : n.-tuple T) :
  select_binarysearch i s = Select b i (in_tuple s).
Proof.
rewrite /select_binarysearch binarysearchE /Intervalsearch /Select //=.
- case: ex_minnP => m /= Hm Hall.
  case: ex_minnP => m' /= Hm' Hall'.
  rewrite !RankE /= in Hm Hm'.
  have Hmm': m <= m'.
    apply Hall.
    move/orP: Hm' => [|] /andP [-> /= HR'].
      by rewrite HR'.
    by rewrite orbT.
  have Hm'm: m' <= m.
    apply Hall'.
    rewrite RankE /=.
    move/orP: Hm => [/andP [-> ->]|Hm] //.
    rewrite Hm.
    case/orP: Hm' => [|] /andP [] Hm' HR'.
      move: (leq_trans Hmm' Hm').
      by rewrite (eqP Hm) ltnn.
    by rewrite HR' orbT.
  move/andP: (conj Hmm' Hm'm).
  by rewrite -eqn_leq => /eqP.
- by apply rank_incr.
Qed.

End select_prop.

Module rank_select_test.

Local Notation "0" := false.
Local Notation "1" := true.

Definition s : seq bool := [:: 1; 0; 0; 1;
                               0; 1; 0; 0;
                               1; 1; 1; 0;
                               0; 1; 0; 0;
                               1; 1; 0; 1;
                               0; 0; 0; 0;
                               1; 1; 1; 1;
                               0; 1; 0; 0;
                               1; 0; 0; 1;
                               1; 0; 0; 1;
                               0; 1; 0; 0;
                               0; 1; 0; 0;
                               0; 1; 0; 1;
                               0; 1; 0; 1;
                               1; 0].
Eval compute in size s.
Eval compute in rank true 4 s.  (* 2 *)
Eval compute in rank true 36 s. (* 17 *)
Eval compute in rank true 57 s. (* 26 *)
Eval compute in rank true 58 s. (* 26 *)
Eval compute in select true 2 s. (* 4 *)
Eval compute in select true 17 s. (* 26 *)
Eval compute in select true 26 s. (* 57 *)
Eval compute in select true 27 s. (* 59 *)

End rank_select_test.

Section jacobson_rank_directories.

Section first_level_dir.

Variables (T : eqType) (b : T) (sz : nat).
Implicit Type s : seq T.

Definition first_level_dir s :=
  [seq rank b (x * sz) s | x <- iota 1 (size s %/ sz)].

Lemma first_level_dir_rank i s : i < size s %/ sz ->
  nth 0 (first_level_dir s) i = rank b (i.+1 * sz) s.
Proof.
move=> H.
rewrite /first_level_dir (nth_map 0); last by rewrite size_iota (leq_trans H) // leq_addr.
rewrite nth_iota; last by rewrite (leq_trans H) // leq_addr.
by rewrite add1n.
Qed.

Lemma first_level_dir_cut s : 0 < sz ->
  first_level_dir s = first_level_dir (take (size s %/ sz * sz) s).
Proof.
move=> sz0.
apply (@eq_from_nth _ O).
  rewrite /first_level_dir 2!size_map 2!size_iota size_take.
  rewrite {3}(divn_eq (size s) sz).
  case: ifP => // _; by rewrite mulnK.
move=> i.
rewrite /first_level_dir size_map size_iota => Hi.
rewrite (nth_map O); last by rewrite size_iota.
rewrite (nth_map O); last first.
  by rewrite size_iota size_take; case: ifP => //; rewrite mulnK.
rewrite size_take.
case: ifP => _.
  by rewrite mulnK // {2}/rank take_take // nth_iota // add1n leq_pmul2r.
by rewrite {2}/rank take_take // nth_iota // add1n leq_pmul2r.
Qed.

End first_level_dir.

Section second_level_dir.

Variables (T : eqType) (b : T) (sz2 : nat).
Implicit Type s : seq T.

Definition second_level_dir k s :=
  let sz1 := k * sz2 in
  let firsts := [seq (take (sz1 - sz2) x) | x <- shape_dir sz1 s] in
  let last := drop (size s %/ sz1 * sz1) s in
  [seq first_level_dir b sz2 x | x <- rcons firsts last].

Definition second_level_dir_head k s :=
  let sz1 := k * sz2 in
  [seq first_level_dir b sz2 (take (sz1 - sz2) x) | x <- shape_dir sz1 s].

Definition second_level_dir_tail k s :=
  let sz1 := k * sz2 in
  first_level_dir b sz2 (drop (size s %/ sz1 * sz1) s).

Lemma size_second_level_dir_head k s :
  let sz1 := k * sz2 in
  size (second_level_dir_head k s) = size s %/ sz1.
Proof.
move=> sz1.
by rewrite /second_level_dir_head size_map /shape_dir size_reshape size_nseq.
Qed.

Hypothesis sz2_neq0 : 0 < sz2.

Lemma small_neq0 k i :
  let sz1 := k * sz2 in
  let small := (i %% sz1) %/ sz2 in
  sz2 <= i %% sz1 ->
  0 < small.
Proof.
move=> sz1 small H6.
rewrite /small.
have /eqP H2 : sz2 %/ sz2 == 1 by rewrite divnn sz2_neq0.
by rewrite -ltnS -H2 ltnS leq_div2r.
Qed.

Lemma second_level_dir_tail_rank i k' s :
  let k := k'.+1 in
  let sz1 := k * sz2 in
  let big := i %/ sz1 in
  let small := (i %% sz1) %/ sz2 in
  i <= size s ->
  sz2 <= i %% sz1 ->
  size s %/ sz1 <= big ->
  nth 0 (second_level_dir_tail k s) small.-1 =
  rank b (small * sz2) (drop (big * sz1) s).
Proof.
move=> k sz1 big small H3 H1 H2.
have Hsmall : 0 < small.
  by rewrite small_neq0.
rewrite /second_level_dir_tail -/sz1 first_level_dir_rank; last first.
  rewrite size_drop -/sz1 {1}(divn_eq (size s) sz1) addnC addnK -ltnS prednK // ltnS leq_div2r //.
  move/(congr1 (fun x => x - i %/ sz1 * sz1)) : (divn_eq i sz1); rewrite addnC addnK => <-.
  move/(congr1 (fun x => x - size s %/ sz1 * sz1)) : (divn_eq (size s) sz1); rewrite addnC addnK => <-.
  rewrite leq_sub //.
  by rewrite leq_pmul2r // /sz1 mulSn ltn_addr.
rewrite prednK // -/sz1.
suff -> : size s %/ sz1 = big by done.
rewrite /big.
apply/eqP.
by rewrite eqn_leq andbC leq_div2r // ltnW.
Qed.

Lemma last_small_block_never_addressed i k' (sz20 : 0 < sz2) :
  let k := k'.+1 in
  let sz1 := k * sz2 in
  let small := (i %% sz1) %/ sz2 in
  sz2 <= i %% sz1 -> small.-1 < k - 1.
Proof.
move=> k sz1 small sz2i1.
rewrite /small -ltnS prednK; last first.
  apply (@leq_trans (sz2 %/ sz2)); by [rewrite divnn sz20 | apply leq_div2r].
by rewrite subn1 /= -/k ltn_divLR // ltn_mod /sz1 mulSn addn_gt0 sz20.
Qed.

Lemma second_level_dir_head_rank i k' s :
  0 < sz2 ->
  let k := k'.+1 in
  let sz1 := k * sz2 in
  let big := i %/ sz1 in
  let small := (i %% sz1) %/ sz2 in
  i <= size s ->
  0 < small ->
  sz2 <= i %% sz1 ->
  big < size s %/ (k * sz2) ->
  nth 0 (nth [::] (second_level_dir_head k s) big) small.-1 =
  rank b (small * sz2) (drop (big * sz1) s).
Proof.
move=> H1 k sz1 big small H3 Hsmall H6 H2.
rewrite /second_level_dir_head (nth_map [::]); last first.
  by rewrite /shape_dir size_reshape size_nseq.
rewrite -/sz1 /shape_dir reshape_nseq_drop (nth_map O); last by rewrite size_iota.
rewrite nth_iota // add0n take_take; last by rewrite leq_subr.
rewrite first_level_dir_rank; last first.
  rewrite size_take size_drop.
  case: ifP => [|/negbT] H4.
    apply: (@leq_trans (k - 1)).
      apply last_small_block_never_addressed => //.
    by rewrite /sz1 /k mulSn addnC addnK mulnK // subn1.
  rewrite -ltnS prednK // ltnS /small leq_div2r // /big.
  move/(congr1 (fun x => x - i %/ sz1 * sz1)) : (divn_eq i sz1); rewrite addnC addnK => <-.
  by rewrite leq_sub // ltnW.
rewrite prednK // rank_take // -leq_divRL // -ltnS /sz1 mulSn addnC addnK mulnK //.
move: (last_small_block_never_addressed H1 H6).
by rewrite -/k -/sz1 -/small -ltnS prednK // subn1.
Qed.

Lemma second_level_dir_rank i k' s :
 0 < sz2 ->
 i <= size s ->
 let k := k'.+1 in
 let sz1 := k * sz2 in
 let big := i %/ sz1 in
 let small := (i %% sz1) %/ sz2 in
 sz2 <= i %% sz1 ->
 nth 0 (nth [::] (second_level_dir k s) big) small.-1 =
 rank b (small * sz2) (drop (big * sz1) s).
Proof.
move=> H1 H3 k sz1 big small H6.
have Hsmall : 0 < small by rewrite small_neq0.
rewrite /second_level_dir.
rewrite map_rcons -cats1 nth_cat -map_comp size_second_level_dir_head.
case: ifP => [H2 | /negbT]; last first.
  rewrite -leqNgt => H2.
  set tmp := big - _.
  have {tmp}->/= : tmp = 0 by apply/eqP; rewrite subn_eq0 /big leq_div2r // ltnW.
  by rewrite second_level_dir_tail_rank.
by rewrite second_level_dir_head_rank.
Qed.

End second_level_dir.

Section storage_dir.

Variables (T : eqType) (b : T).
Implicit Type s : seq T.

Lemma upper_bound_for_first_level_dir_entries sz1 s :
  forall n, n \in first_level_dir b sz1 s -> n <= size s.
Proof. move=> n /mapP[m ? ->]; by rewrite rankE Rank_ub. Qed.

Lemma upper_bound_for_second_level_dir_head_entries k sz2 s :
  let sz1 := k * sz2 in
  forall e, e \in flatten (second_level_dir_head b sz2 k s) -> e <= sz1.
Proof.
move=> sz1 /= e /flattenP[/= small].
move=> /mapP[/= big Hbig ->{small}].
move/upper_bound_for_first_level_dir_entries/leq_trans; apply.
move: Hbig.
rewrite /shape_dir reshape_nseq_drop.
move/mapP => [/= big_idx _ ->{big}].
rewrite take_take ?leq_subr //.
rewrite size_take size_drop.
case: ifP => [_|/negbT]; first by rewrite leq_subr.
rewrite -leqNgt.
move/leq_trans; apply; by rewrite leq_subr.
Qed.

Lemma mem_size_second_level_dir_head k' sz2 s l :
  let k := k'.+1 in
  0 < sz2 -> l \in second_level_dir_head b sz2 k s ->
  size l = k'.
Proof.
move=> k sz20 /mapP [s'_].
rewrite /shape_dir reshape_nseq_drop.
case/mapP => /= i.
rewrite mem_iota leq0n /= add0n => Hi -> ->.
rewrite take_take; last by rewrite leq_subr.
rewrite /first_level_dir size_map size_iota.
rewrite size_take size_drop.
case: ifP => [H | /negbT].
  clear H.
  by rewrite mulSn addnC addnK mulnK.
rewrite -leqNgt => H.
rewrite [in X in _ <= X]mulSn addnC addnK in H.
move: (leq_div2r sz2 H).
rewrite mulnK // => {H}H.
have H' : k' * sz2 <= size s - i * (k * sz2).
  rewrite -(leq_add2l (i * (k * sz2))).
  rewrite addnBA; last first.
    rewrite -leq_divRL.
      by rewrite ltnW.
    by rewrite /k mulSn ltn_addr.
  rewrite [in X in _ <= X]addnC addnK.
  rewrite leq_divRL in Hi; last first.
    by rewrite /k mulSn ltn_addr.
  rewrite mulSn addnC {2}/k {2}mulSn in Hi.
  apply: (leq_trans _ Hi).
  rewrite leq_add2l.
  by rewrite leq_addl.
apply/eqP.
rewrite eqn_leq H /=.
by rewrite leq_divRL //.
Qed.

Lemma size_flatten_second_level_dir_head sz2 s k'  :
  0 < sz2 ->
  let k (* number of small blocks in a big block *) := k'.+1 in
  let n := size s in
  let sz1 := k * sz2 in
  size (flatten (second_level_dir_head b sz2 k s)) = n %/ sz1 * k.-1.
Proof.
move=> Hsz2 k n sz1.
rewrite -sum1_size.
rewrite big_flatten /=.
rewrite big_seq_cond.
rewrite (eq_bigr (fun=> k.-1)); last first.
  move=> /= i.
  rewrite andbT => Hi.
  rewrite sum1_size.
  by apply: mem_size_second_level_dir_head Hi.
rewrite -big_seq_cond.
rewrite big_const_seq iter_addn addn0.
rewrite mulnC.
rewrite count_predT.
by rewrite /second_level_dir_head size_map /shape_dir size_reshape size_nseq.
Qed.

End storage_dir.

End jacobson_rank_directories.

Section jacobson_rank_algorithm.

Variables (T : eqType) (b : T).
Implicit Type s : seq T.
Variable (sz2 : nat).

Definition jacobson_rank k i s :=
  let sz1 := k * sz2 in
  let dir1 := first_level_dir b sz1 s in
  let dir2 := second_level_dir b sz2 k s in
  let big := i %/ sz1 in
  let small := (i %% sz1) %/ sz2 in
  (if sz1 <= i then nth 0 dir1 big.-1 else 0) +
  (if sz2 <= i %% sz1 then nth 0 (nth [::] dir2 big) small.-1 else 0) +
  rank b (i %% sz2) (drop (big * sz1 + small * sz2) s).

Lemma jacobson_rank_rank s k' i :
  0 < sz2 -> i <= size s ->
  let k := k'.+1 in
  jacobson_rank k i s = rank b i s.
Proof.
move=> H1 H3 k.
pose sz1 := k * sz2. pose big := i %/ sz1. pose small := (i %% sz1) %/ sz2.
rewrite [in RHS](divn_eq i sz1) rank_addn // -/big.
rewrite /jacobson_rank -/sz1 -addnA.
congr addn.
  case: ifP => [sz1i | /negbT]; last first.
    by rewrite -ltnNge => szi; rewrite /big divn_small // mul0n rank0.
  rewrite first_level_dir_rank //; last first.
    rewrite -ltnS prednK; last by rewrite divn_gt0 // /sz1 mulSn ltn_addr.
    by rewrite ltnS leq_div2r // ltnW.
  by rewrite prednK // divn_gt0 // /sz1 mulSn ltn_addr.
rewrite [in RHS](divn_eq (i %% sz1) sz2).
rewrite [in RHS]rank_addn.
congr addn.
  rewrite -/big -/small.
  case: ifP => [H6|/negbT]; last first.
    rewrite -ltnNge => ?; by rewrite /small divn_small // mul0n /rank take0.
  by rewrite second_level_dir_rank.
by rewrite -/small -/sz1 drop_drop addnC {1}(divn_eq i sz1) {2}/sz1 mulnA modnMDl.
Qed.

End jacobson_rank_algorithm.

Module test.

Definition b := [seq 0 < x | x <- [:: 1;0;0;1;  0;1;0;0;  1;1;1;0;  0;1;0;0;
                               1;1;0;1;  0;0;0;0;  1;1;1;1;  0;1;0;0;
                               1;0;0;1;  1;0;0;1;  0;1;0;0;  0;1;0;0] ].

Compute first_level_dir true 16 b.
Compute rank true 36 b.
Compute second_level_dir_head true 16 4 b.
Compute jacobson_rank true 16 4 36 b.

End test.
