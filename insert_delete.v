From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section insert_delete.

  Variable T : Type.

  Definition insert (s t : seq T) i :=
    take i s ++ t ++ drop i s.

  Lemma insert_nil s i : insert s [::] i = s.
  Proof. by rewrite /insert /= cat_take_drop. Qed.

  Definition insert1 s x i := insert s [:: x] i.

  Lemma insert_catL s b i t : i < size s ->
    insert (s ++ t) b i = insert s b i ++ t.
  Proof. move=> si; by rewrite /insert take_cat drop_cat si -2!catA. Qed.

  Lemma insert_catR s b i t : i >= size s ->
    insert (s ++ t) b i = s ++ insert t b (i - size s).
  Proof. move=> si; by rewrite /insert take_cat drop_cat ltnNge si /= -catA. Qed.

  Lemma size_insert (s : seq T) x i : size (insert s x i) = size s + size x.
  Proof. by rewrite /insert -{3}(cat_take_drop i s) !size_cat addnAC addnA. Qed.

  Lemma size_insert1 s (x : T) n : size (insert1 s x n) = (size s).+1.
  Proof. by rewrite size_insert addn1. Qed.

  Lemma size_insert1_pos (s : seq T) x i : size (insert1 s x i) > 0.
  Proof. by rewrite size_insert1. Qed.

  Lemma nth_insert1 (s : seq T) x0 x i :
    i <= size s -> nth x0 (insert1 s x i) i = x.
  Proof.
    move=> His. rewrite /insert1 nth_cat.
    by rewrite ifF size_takel // ?ltnn // subnn.
  Qed.

  Lemma insert_cat s t v i :
    insert s (t ++ v) i = insert (insert s t i) v (i + size t).
  Proof.
  elim: s t v i => [s1 s2 i|x1 x2 IH x v [|i]]; rewrite /insert.
    by rewrite ?(take_oversize,leq_addl,drop_oversize,cats0).
  by rewrite /= add0n ?(take_cat,ltnn,subnn,take0,cats0,drop_cat,drop0,catA).
  by rewrite addSn /= -/(insert _ _ _) IH.
  Qed.

  Lemma insert_head (s xs : seq T) x i :
    insert s (x :: xs) i = insert (insert1 s x i) xs i.+1.
  Proof. by rewrite -cat1s insert_cat addn1. Qed.
    
  Definition delete (s : seq T) i :=
    take i s ++ drop (i.+1) s.

  Lemma delete_nil i : delete [::] i = [::].
  Proof. by []. Qed.
  
  Lemma size_take_leq i (s : seq T) : size (take i s) <= i.
  Proof. rewrite size_take; case: ifP => Hi //; by rewrite leqNgt Hi. Qed.
    
  Lemma nth_delete (s : seq T) i x0 n :
    nth x0 (delete s i) n = if n >= i then nth x0 s (n.+1)
                            else nth x0 s n.
  Proof.
    elim: s n i => [|h t IHt] //= n i.
    by rewrite delete_nil nth_nil if_same.
      rewrite /delete. rewrite /delete in IHt.
      case: i => //=. by rewrite drop0.
      move => i. case: n => // n.
        by rewrite ltnS -IHt.
  Qed.
  
  Lemma size_delete (s : seq T) i :
    i < size s -> size (delete s i) = (size s).-1.
  Proof.
    rewrite /delete size_cat size_take size_drop => Hi.
    rewrite Hi -addn1 -subn1 addnBA addnC //=.
      by rewrite subnDA addnK.
  Qed.
    
  Lemma delete_insert1 (s : seq T) x i :
    i <= size s -> delete (insert1 s x i) i = s.
  Proof.
    move=> His.
    rewrite /delete /insert1 take_cat ifF size_takel // ?ltnn //.
    rewrite subnn /= cats0 drop_cat size_takel // ifF.
      by rewrite -addn1 addKn /= drop0 cat_take_drop.
    by rewrite ltnNge leqnSn.
  Qed.
  
End insert_delete.

Section insert_delete_eqtype.
  Variable T : eqType.

  Lemma in_drop_take (s : seq T) x i :
    x \in s -> (x \in (take i s)) || (x \in (drop i s)).
  Proof. by rewrite -mem_cat cat_take_drop. Qed.

  Lemma in_insert1 (s : seq T) x0 x i :
    x0 \in s -> x0 \in (insert1 s x i).
  Proof. move=> Hi; by rewrite mem_cat in_cons orbCA in_drop_take // orbT. Qed.

  Lemma count_insert (b : T) s t n :
    count_mem b (insert s t n) = count_mem b s + count_mem b t.
  Proof. by rewrite !count_cat addnCA -count_cat cat_take_drop addnC. Qed.

  Lemma count_insert1 (b : T) s x n :
    count_mem b (insert1 s x n) = count_mem b s + (x == b).
  Proof. by rewrite /insert1 count_insert /= addn0. Qed.

End insert_delete_eqtype.

Section insert_delete_rank.
Variable A : eqType.

  Lemma rank_insert1 (s : seq A) b0 b i :
    rank b0 (size (insert1 s b i)) (insert1 s b i) =
    if b == b0 then 1 + rank b0 (size s) s else rank b0 (size s) s.
  Proof. rewrite /rank !take_size count_insert1 addnC; by case: ifP. Qed.

  (* Obvious corollary *)
  Corollary rank_insert1_geq (s : seq A) b0 b i :
    rank b0 (size (insert1 s b i)) (insert1 s b i) >= rank b0 (size s) s.
  Proof. rewrite rank_insert1. case: (b == b0) => //. Qed.

  Lemma rank_insert (s t : seq A) b0 i :
    rank b0 (size (insert s t i)) (insert s t i) =
    rank b0 (size s) s + rank b0 (size t) t.
  Proof. by rewrite /rank !take_size count_insert addnC. Qed.
    
End insert_delete_rank.

Section delete_with_return.

  Variable T : Type.
  
  Definition delete_ret x0 (s : seq T) i := (take i s ++ drop (i.+1) s,
                                          nth x0 s i).

  Lemma delete_delete_ret x0 (s : seq T) i :
    delete_ret x0 s i = (delete s i, nth x0 s i).
  Proof. by rewrite /delete /delete_ret. Qed.
  
  Lemma delete_ret_oversize x0 (s : seq T) i :
    i >= size s -> delete_ret x0 s i = (s, x0).
  Proof.
    move => H. rewrite /delete_ret take_oversize. rewrite drop_oversize.
    by rewrite cats0 nth_default. apply: leq_trans. apply: H. exact: leqnSn.
    exact: H.  
  Qed.

  Lemma delete_ret_insert1 x0 (s : seq T) x i :
    i <= size s -> delete_ret x0 (insert1 s x i) i = (s, x).
  Proof.
    move => His.
    rewrite delete_delete_ret. rewrite delete_insert1. by rewrite nth_insert1.
    exact: His.
  Qed.
    
End delete_with_return.