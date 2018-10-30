From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import compact_data_structures rank_select.

(** A formalization of the pred and succ functions *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section pred_and_succ.

Variable T : finType.

Definition pred (b : T) (s : seq T) y := select b (rank b y s) s.

Theorem pred_is_self b (s : seq T) j :
  rank b 1 (drop j s) = 1 -> pred b s j.+1 = j.+1.
Proof.
move=> H.
rewrite -(addn1 j) /pred rank_addn H addn1.
elim: j s H => [|j IH] [|a s] //=; rewrite rank_cons.
  case: ifPn; by rewrite !rank0 addn0 // select0.
case: (a == b) => /= Hrk; by rewrite ?add0n IH.
Qed.

Lemma pred_same_of_rank (b : T) m i B :
  rank b i (drop m B) = 0 -> pred b B (m+i) = pred b B m.
Proof.
elim: m B => [|m IH] B.
  by rewrite drop0 /pred rank0 add0n => ->.
case: B => [|a B] //= /IH.
rewrite /pred /= addSn 2!rank_cons.
case: (a == b) => /=.
  by move ->.
rewrite !add0n.
case Hr: (rank b (m+i) B);
case Hr': (rank b m B) => //.
+ by rewrite rank_addn Hr' addSn in Hr.
+ rewrite select0. by destruct B.
+ by move => ->.
Qed.

Lemma predP b y n (s : n.-tuple T) :
  y <= n ->
  b \notin \bigcup_(i : [1,n] | pred b s y < i <= y) [set tacc s i].
Proof.
move=> yn.
apply/bigcupP => -[i /andP[yi iy]].
rewrite inE => /eqP Hnth.
move: yi.
rewrite /pred -SelectE -RankE /Select.
case: ex_minnP => m /orP [|] /andP [Hm Hy] Hall mi.
  move: Hy.
  rewrite eqn_leq => /andP[_].
  rewrite /Rank.
  set B := (X in #|X| <= _ -> _).
  set A := (X in _ <= #|X| -> _).
  have AB : A \subset B.
    subst A B.
    apply/subsetP => x.
    rewrite !inE => /andP[xm ->].
    by rewrite (leq_trans _ iy) // (leq_trans xm) // ltnW.
  move/(conj AB)/andP.
  rewrite -eqEcard.
  move/eqP/setP/(_ i).
  by rewrite !inE /= leqNgt mi iy /= Hnth eqxx.
move: mi.
by rewrite (eqP Hm) ltnNge ltnW.
Qed.

Definition succ (b : T) (s : seq T) y := select b (rank b y.-1 s).+1 s.

Lemma ltn_succ s b x (xs : x <= size s) : x < succ b s x.+1.
Proof.
elim: s x xs => // s1 s2 IH -[//| x /=].
rewrite /= ltnS => /IH{IH} H; apply: (leq_ltn_trans H) => {H}.
rewrite /succ /=; case: ifPn => [/eqP ->{s1}|s10].
- by rewrite ltnS select_incr // rank_cons eqxx add1n.
- by rewrite ltnS rank_cons (negbTE s10) add0n.
Qed.

Lemma succ_drop (b : T) B n :
  size B > n ->
  succ b B n.+1 - n.+1 = (select b 1 (drop n B)).-1.
Proof.
elim: n B => [|n IH] B.
  by rewrite drop0 /succ rank0 subn1.
case: B => [|a B] //=.
rewrite ltnS => Hn.
rewrite /succ.
destruct n => /=.
  rewrite subSS subn1 rank_cons rank0 addn0 drop0.
  by case: (a == b).
rewrite -IH{} //.
rewrite /succ /= rank_cons subSS.
by case: (a == b).
Qed.

Lemma succP b n (s : n.-tuple T) (y : [1, n]) :
  b \notin \bigcup_(i : [1,n] | y <= i < succ b s y) [set tacc s i].
Proof.
apply/bigcupP => -[i /andP[yi iy]].
rewrite inE => /eqP Hnth.
move: iy.
rewrite /succ -SelectE -RankE /Select.
case: ex_minnP => m /orP[|] /andP [Hm /eqP rankmy] Hall im.
  move: (rankmy) => [:Hm'].
  have @m' : [1,n].
    apply: (@idx.mkt _ (@Ordinal _ m _) _).
    abstract: Hm'.
    apply/negP => /eqP/(congr1 val)/eqP/=; apply/negP.
    by rewrite -lt0n (leq_trans _ im).
  rewrite /Rank -(cardsID [set m'] [set k : [1,n] | k <= m & tacc s k == b]).
  rewrite [X in X + _ = _ -> _](_ : _ = 1); last first.
    apply (@eq_card1 _ m') => /= k.
    rewrite in_setI !inE.
    case/boolP : (k == m') => [/eqP km'|]; [rewrite andbT|by rewrite andbF].
    rewrite km' leqnn /=.
    apply/negPn/negP => Hnth'.
    suff : m <= m.-1 by rewrite leqNgt prednK // ?lt0n // leqnn.
    apply Hall => /=.
    rewrite (leq_trans (leq_pred m) Hm) /= -rankmy.
    apply/orP/or_introl.
    rewrite subset_leqif_cards.
      apply/eqP/setP => p.
      rewrite !inE.
      rewrite -ltnS.
      rewrite ltn_neqAle.
      rewrite -[in RHS](ltn_predK im) /=.
      case /boolP: (@idx.i _ p == m.-1.+1 :> nat) => //= Hk.
      suff /negbTE -> : tacc s p != b by rewrite !andbF.
      suff -> : p = m' by [].
      apply/val_inj/val_inj => /=.
      by rewrite (eqP Hk) prednK // (leq_trans _ im).
    apply/subsetP => p.
    by rewrite !inE => /andP[/leq_trans/(_ (leq_pred m))] -> ->.
  rewrite add1n => -[] /esym/eqP; rewrite subset_leqif_cards.
    move=> [:Hi'].
    have @i' : [1,n].
      apply: (@idx.mkt _ (@Ordinal _ i _) _).
      abstract: Hi'.
      by case: i yi Hnth im.
    move/eqP/setP/(_  i').
    rewrite !inE /=.
    have -> : i' = i by apply/val_inj/val_inj.
    rewrite -Hnth eqxx (ltnW im) 3!andbT.
    by rewrite leqNgt prednK // yi /= neq_ltn /= im.
  apply/subsetP => k.
  rewrite !inE neq_ltn /=.
  case /boolP: (k <= y.-1) => //= Hk ->; rewrite andbT.
  rewrite (leq_eqVlt k) orbC -orb_andl (leq_trans _ im) ?orbT //.
  by rewrite ltnS (leq_trans Hk) // (leq_trans _ yi) // leq_pred.
move: rankmy.
rewrite RankE /rank subSS -[in count_mem b s](cat_take_drop y.-1 s).
rewrite count_cat.
move=> /eqP; apply/negP; rewrite -ltnNge -leq_subLR subSn // subnn.
rewrite -has_count; apply/hasP.
exists b; last by rewrite inE.
rewrite Hnth.
apply/(nthP b).
exists (i.-1 - y.-1).
  rewrite size_drop size_tuple /= ltn_sub2r //.
    by rewrite prednK // idx_leq.
  by rewrite prednK // ?lt0n // -ltnS.
by rewrite (@taccE _ b) nth_drop subnKC // -!subn1 leq_sub2r.
Qed.

End pred_and_succ.
