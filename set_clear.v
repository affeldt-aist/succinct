From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section update.

  Variable T : Type.

  (* Simple wrapper around set_nth to stop the padding behavior 
   * of set_nth, which is confusing
   *)
  Definition update (s : seq T) x i :=
    if i < size s then set_nth x s i x else s.

  Lemma set_nth_default_sizel (s : seq T) y y' x i :
    i < size s -> set_nth y s i x = set_nth y' s i x.
  Proof. elim: s i => [|h t IHt] [|j] //= H. by rewrite IHt. Qed.
  
  Lemma size_update (s : seq T) x i :
    size s = size (update s x i).
  Proof.
    rewrite /update. case: ifP => Hi.
    by rewrite size_set_nth maxnE subnKC. exact.
  Qed.

  Lemma update_cons (s : seq T) h x i :
    update (h::s) x i.+1 = h :: update s x i.
  Proof. rewrite /update /= ltnS; by case: ifPn. Qed.

  Lemma update_ith (s : seq T) x0 x i :
    i < size s -> nth x0 (update s x i) i = x.
  Proof.
    move => H. rewrite /update H.
    rewrite (set_nth_default_sizel x x0 x H).
    by rewrite nth_set_nth //= eq_refl.
  Qed.

  Lemma update_jth (s : seq T) x0 x i j :
    i != j -> nth x0 (update s x i) j = nth x0 s j.
  Proof.
    move => H. rewrite /update. case: ifP => // Hsize.
    rewrite (set_nth_default_sizel x x0 x Hsize).
    by rewrite nth_set_nth //= ifN // eq_sym.
  Qed.

  Lemma update_oversize (s : seq T) x i :
    i >= size s -> update s x i = s.
  Proof. by rewrite /update ltnNge => ->. Qed.
  
  Lemma update_cat (s t : seq T) x i :
    update (s ++ t) x i = if i < size s
                          then (update s x i) ++ t
                          else s ++ update t x (i - size s).
  Proof.
    elim: s i => [|h s IHs] [|i] //=.
    by rewrite !update_cons subSS cat_cons -(fun_if (cons _)) -IHs.
  Qed.
    
End update.

Section bit_set_clear.

  Definition bit_set (s : seq bool) i := update s true i.

  Definition bit_clear (s : seq bool) i := update s false i.

  Definition bit_toggle (s : seq bool) i :=
    update s (~~ (nth true s i)) i.

  Lemma size_bit_set (s : seq bool) i : size (bit_set s i) = size s.
  Proof. rewrite /bit_set. by rewrite (size_update s true i). Qed.

  Lemma size_bit_clear (s : seq bool) i : size (bit_clear s i) = size s.
  Proof. rewrite /bit_set. by rewrite (size_update s false i). Qed.

  Lemma bit_set_over (s : seq bool) i : i >= size s -> bit_set s i = s.
  Proof. rewrite /bit_set /update leqNgt. by move/negbTE => ->. Qed.
  
  Lemma nth_bit_set (s : seq bool) b0 i :
    i < size s -> nth b0 (bit_set s i) i = true.
  Proof. move => H. by rewrite /bit_set update_ith. Qed.

  Lemma nth_bit_clear (s : seq bool) b0 i :
    i < size s -> nth b0 (bit_clear s i) i = false.
  Proof. move => H. by rewrite /bit_clear update_ith. Qed.

  Lemma count_bit_set (s : seq bool) b0 i : i < size s ->
    count_mem true (bit_set s i) = ~~ (nth b0 s i) + count_mem true s.
  Proof.
    elim: s i => [|b s IHs] [|j] //=.
      by case: b.
    rewrite ltnS => /= Hi.
    by rewrite addnCA -IHs // /bit_set update_cons.
  Qed.
    
  Lemma true_count_pos (s : seq bool) b0 i :
    i < size s -> nth b0 s i -> count_mem true s > 0.
  Proof.
    elim: s i => [|b s IHs] //= [|i] Hi /= Hnth.
      by rewrite Hnth.
    by rewrite addn_gt0 (IHs i) // orbT.
  Qed.
  
  Lemma count_bit_clear (s : seq bool) b0 i : i < size s ->
    count_mem true (bit_clear s i) = count_mem true s - nth b0 s i.
  Proof.
    elim: s i => [|b s IHs] [|j] //=.
      case: b => /=; by rewrite ?addKn ?subn0.
    rewrite ltnS => /= Hj.
    rewrite -addnBA; last first.
      case Hnth: (nth b0 s j) => //.
      exact: (true_count_pos Hj Hnth).
    by rewrite -IHs // /bit_clear update_cons.
  Qed.

  Lemma count_bit_toggle (s : seq bool) b0 i :
    i < size s -> count_mem true (bit_toggle s i) =
                  if nth b0 s i
                  then count_mem true s - 1
                  else count_mem true s + 1.
  Proof.
    rewrite /bit_toggle /update => H; rewrite H.
    elim: s i H => [|b s IHs] [|j] //=.
      by case Hb: b => //=; rewrite add1n add0n ?addn1 // subn1 succnK.
    rewrite ltnS => H.
    rewrite IHs //; case: ifP => Hnth.
      by rewrite addnBA // (true_count_pos H Hnth).
    by rewrite addnA.
  Qed.

End bit_set_clear.
