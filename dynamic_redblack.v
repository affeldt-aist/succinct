From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import compact_data_structures rank_select insert_delete set_clear.

(** * A formalization of succinct dynamic bit vectors *)

(** OUTLINE:
  0. Section btree
  1. Section dtree
       Definition daccess, drank, dselect_1 and dselect_0.
  2. Section insert
  3. Section dinsert
  4. Section set_clear
  5. Section delete
  6. Section ddelete
  7. Section example
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac decompose_rewrite :=
  let H := fresh "H" in
  case/andP || (move=>H; rewrite ?H ?(eqP H)).

Ltac decomp ok := move: ok => /=; repeat decompose_rewrite.

Section btree.

Variables D A : Type.

Inductive color := Red | Black.

Inductive btree : Type :=
  | Bnode : color -> btree -> D -> btree -> btree
  | Bleaf : A -> btree.

End btree.

Section eq_btree.

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

Variables D A : eqType.

Fixpoint eq_btree (t1 t2 : btree D A) := 
  match t1,t2 with
  | Bleaf a, Bleaf b => a == b
  | Bnode c1 l1 d1 r1, Bnode c2 l2 d2 r2 =>
    (d1 == d2) && (c1 == c2) && (eq_btree l1 l2) && (eq_btree r1 r2)
  | Bnode _ _ _ _, Bleaf _ 
  | Bleaf _, Bnode _ _ _ _ => false
  end.

Lemma eq_dtree_refl (t : btree D A) : eq_btree t t.
Proof. elim t => [? l H1 ? r H2 /=|a //=]; by rewrite H1 H2 !eq_refl. Qed.

Lemma eq_dtree_iff t1 t2 : t1 = t2 <-> eq_btree t1 t2.
Proof.
  split => [->|]; first by rewrite eq_dtree_refl.
  move: t1 t2;
    elim => [? l1 lH1 ? r1 rH1|?]; elim => [? l2 lH2 ? r2 rH2 H|?] //;
  last by move/eqP => /= ->.
  move/andP: H; case; move/andP; case;
    move/andP; case; move/eqP => ->; move/eqP => -> H1 H2.
  by rewrite (lH1 _ H1) (rH1 _ H2).
Qed.

Lemma btree_eqP : Equality.axiom eq_btree.
Proof.
  move; case => [? l1 ? r1 |?]; case => [? l2 ? r2|?] //;
  set b:= (eq_btree _ _); case Hb : b; subst b;
  try (apply ReflectT; apply eq_dtree_iff => //); try apply ReflectF => //.
   by case => H1 H2 H3 H4; move: Hb; rewrite H1 H2 H3 H4 eq_dtree_refl.
  by case => H1; move: Hb; rewrite H1 eq_dtree_refl.
Qed.

Canonical btree_eqMixin := EqMixin btree_eqP.
Canonical btree_eqType := Eval hnf in EqType (btree D A) btree_eqMixin.

End eq_btree.

Section dtree.

Definition dtree := btree (nat * nat) (seq bool).

Fixpoint daccess (B : dtree) (i : nat) :=
  match B with
  | Bnode _  l (num, ones) r =>
    if i < num then daccess l i else daccess r (i - num)
  | Bleaf s =>
    nth false s i
  end.

Fixpoint drank (B : dtree) (i : nat) :=
  match B with
  | Bnode _ l (num, ones) r =>
    if i < num then drank l i else ones + drank r (i - num)
  | Bleaf s =>
    rank true i s
  end.

Fixpoint dflatten (B : dtree) :=
  match B with
  | Bnode _ l _ r => dflatten l ++ dflatten r
  | Bleaf s => s
  end.

Fixpoint dselect_1 (B : dtree) (i : nat) :=
  match B with
  | Bnode _ l (num, ones) r =>
    if i <= ones then dselect_1 l i else num + dselect_1 r (i - ones)
  | Bleaf s => select true i s
  end.

Fixpoint dselect_0 (B : dtree) (i : nat) :=
  match B with
  | Bnode _ l (num, ones) r =>
    let zeroes := num - ones
    in if i <= zeroes then dselect_0 l i else num + dselect_0 r (i - zeroes)
  | Bleaf s => select false i s
  end.

Fixpoint dsize (B : dtree) :=
  match B with
  | Bnode _ l (n, _) r => n + dsize r
  | Bleaf s => size s
  end.

Fixpoint dones (B : dtree) :=
  match B with
  | Bnode _ l (_, o) r => o + dones r
  | Bleaf s => count_mem true s
  end.

Notation size_df t := (size (dflatten t)).
Notation ones_df t := (count_mem true (dflatten t)).

Definition access (s : seq bool) i := nth false s i.

Variables low high : nat.  (* (w ^ 2)./2 and (w ^ 2).*2 *)

Fixpoint wf_dtree (B : dtree) :=
  match B with
  | Bnode _ l (num, ones) r =>
    [&& num == size_df l, ones == ones_df l, wf_dtree l & wf_dtree r]
  | Bleaf arr => low <= size arr < high
  end.

Lemma dtree_ind (P : dtree -> Prop) :
  (forall c (l r : dtree) num ones,
      num = size_df l -> ones = ones_df l -> wf_dtree l /\ wf_dtree r ->
      P l -> P r -> P (Bnode c l (num, ones) r)) ->
  (forall s, low <= size s < high -> P (Bleaf _ s)) ->
  forall B, wf_dtree B -> P B.
Proof.
  move=> HN HL; elim => [c l IHl [num ones] r IHr | s] //=.
    move/andP => [/eqP Hones] /andP [/eqP Hnum] /andP [wfl wfr].
    apply: HN; auto.
  by apply: HL.
Qed.

Lemma daccessE (B : dtree) : wf_dtree B -> daccess B =1 access (dflatten B).
Proof.
  move: B.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  by rewrite IHl IHr /access nth_cat.
Qed.

Lemma drankE (B : dtree) i : wf_dtree B ->
  drank B i = rank true i (dflatten B).
Proof.
  move=> wf; move: B wf i.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  rewrite rank_cat ltn_neqAle IHl IHr (rank_size _ _ _ erefl).
  by case: ifP.
Qed.

Lemma dselect_1E (B : dtree) i : wf_dtree B ->
dselect_1 B i = select true i (dflatten B).
Proof.
  move=> wf; move: B wf i.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  by rewrite select_cat IHl IHr.
Qed.

Lemma predC_bool b : predC (pred1 b) =1 pred1 (negb b).
Proof. by case. Qed.

Lemma count_mem_false_true (s : seq bool) :
  count_mem false s + count_mem true s = size s.
Proof.
  by rewrite -(count_predC (pred1 false)) (eq_count (predC_bool false)).
Qed.

Lemma dselect_0E (B : dtree) i : wf_dtree B ->
dselect_0 B i = select false i (dflatten B).
Proof.
  move=> wf; move: B wf i.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  by rewrite select_cat -IHl -IHr -[in X in X - _]count_mem_false_true addnK.
Qed.

Lemma dsizeE (B : dtree) : wf_dtree B -> dsize B = size_df B.
Proof.
  move=> wf; move: B wf.
  apply: dtree_ind => // c l r num ones Hnum Hones _ IHl IHr /=.
  by rewrite Hnum IHr size_cat.
Qed.

Lemma donesE (B : dtree) : wf_dtree B -> dones B = ones_df B.
Proof.
  move=> wf; move: B wf.
  apply: dtree_ind => // c l r num ones Hnum Hones _ IHl IHr /=.
  by rewrite Hones IHr count_cat.
Qed.

Corollary drank_all (B : dtree) :
  wf_dtree B -> drank B (dsize B) = ones_df B.
Proof. move => wf. by rewrite drankE // /rank dsizeE // take_size. Qed.

Definition drank_size B := drank B (dsize B).

End dtree.

Notation size_df t := (size (dflatten t)).
Notation ones_df t := (count_mem true (dflatten t)).

Section insert.

Variables D A : Type.
Variable addD : D -> D -> D.
Variable subD : D -> D -> D.

Definition balance col (l r : btree D A) dl : btree D A :=
  match col with
  | Red => Bnode Red l dl r
  | Black => match l, r with
             | Bnode Red (Bnode Red a da b) dab c, d =>
               Bnode Red (Bnode Black a da b) dab
                         (Bnode Black c (subD dl dab) d)
             | Bnode Red a da (Bnode Red b db c), d =>
               Bnode Red (Bnode Black a da b) (addD da db)
                         (Bnode Black c (subD (subD dl da) db) d)
             | a, Bnode Red (Bnode Red b db c) dbc d =>
               Bnode Red (Bnode Black a dl b) (addD dl db)
                         (Bnode Black c (subD dbc db) d)
             | a, Bnode Red b db (Bnode Red c dc d) =>
               Bnode Red (Bnode Black a dl b) (addD dl db)
                         (Bnode Black c dc d)
             | _, _ => Bnode Black l dl r
             end
  end.

Definition balanceL col (l r : btree D A) dl : btree D A :=
  match col with
  | Red => Bnode Red l dl r
  | Black => match l with
             | Bnode Red (Bnode Red a da b) dab c =>
               Bnode Red (Bnode Black a da b) dab
                         (Bnode Black c (subD dl dab) r)
             | Bnode Red a da (Bnode Red b db c) =>
               Bnode Red (Bnode Black a da b) (addD da db)
                         (Bnode Black c (subD (subD dl da) db) r)
             | _ => Bnode Black l dl r
             end
  end.

Definition balanceR col (l r : btree D A) dl : btree D A :=
  match col with
  | Red => Bnode Red l dl r
  | Black => match r with
             | Bnode Red (Bnode Red b db c) dbc d =>
               Bnode Red (Bnode Black l dl b) (addD dl db)
                         (Bnode Black c (subD dbc db) d)
             | Bnode Red b db (Bnode Red c dc d) =>
               Bnode Red (Bnode Black l dl b) (addD dl db)
                         (Bnode Black c dc d)
             | _ => Bnode Black l dl r
             end
  end.

Variable bins_leaf : A -> bool -> nat -> btree D A.
Variable lt_index : nat -> D -> bool.
Variable right_index : nat -> D -> nat.
Variable insD : D -> bool -> D.

Fixpoint bins (B : btree D A) b i : btree D A :=
  match B with
  | Bleaf s => bins_leaf s b i
  | Bnode c l d r =>
      if lt_index i d
      then balanceL c (bins l b i) r (insD d b)
      else balanceR c l (bins r b (right_index i d)) d
    end.

Definition binsert (B : btree D A) b i : btree D A :=
  match bins B b i with
  | Bleaf s => Bleaf _ s
  | Bnode _ l d r => Bnode Black l d r
  end.

(*
 * Following Appel (2011), pp. 6 - 8
 *
 * ctxt = "color context", or the color of
 * the parent node
 *
 * bh = "black height", i.e. # of black nodes on the
 * path from the root
 *)
Fixpoint is_redblack (B : btree D A) ctxt bh :=
  match B with
  | Bleaf _ => bh == 0
  | Bnode c l _ r =>
    match c, ctxt with
    | Red, Red => false
    | Red, Black => is_redblack l Red bh
                    && is_redblack r Red bh
    | Black, _ => (bh > 0) && is_redblack l Black (bh.-1) &&
                              is_redblack r Black (bh.-1)
    end
  end.

Definition nearly_redblack B bh :=
  match B with
  | Bnode Red l _ r => is_redblack l Black bh && is_redblack r Black bh
  | _ => is_redblack B Black bh
  end.

Hypothesis Hbins_leaf : forall a b i, is_redblack (bins_leaf a b i) Black 0.

Lemma is_redblack_Red_Black B n :
  is_redblack B Red n -> is_redblack B Black n.
Proof. by case: B => /= [[]|]. Qed.

Lemma balanceL_Black_nearly_is_redblack l r n b :
  nearly_redblack l n -> is_redblack r Black n ->
  is_redblack (balanceL Black l r b) Black n.+1.
Proof.
  case: l => [[[[] lll ? llr|?] ? [[] lrl ? lrr|?]|ll ? lr]|?] /=;
    repeat decompose_rewrite => //;
    by rewrite !is_redblack_Red_Black -?(eqP H1).
Qed.

Lemma balanceR_Black_nearly_is_redblack l r n b :
  nearly_redblack r n -> is_redblack l Black n ->
  is_redblack (balanceR Black l r b) Black n.+1.
Proof.
  case: r => [[[[] rll ? rlr|?] ? [[] rrl ? rrr|?]|rl ? rr]|?] /=;
    repeat decompose_rewrite => //;
    by rewrite !is_redblack_Red_Black -?(eqP H1).
Qed.

Lemma is_redblack_nearly_redblack B c n :
  is_redblack B c n -> nearly_redblack B n.
Proof.
  case: B => //= -[]; case: c => // l p r /andP [Hl Hr].
  by rewrite !is_redblack_Red_Black.
Qed.

Lemma bins_is_redblack B b i n :
  (is_redblack B Black n -> nearly_redblack (bins B b i) n) /\
  (is_redblack B Red n -> is_redblack (bins B b i) Black n).
Proof.
  elim: B i n => [c l IHl d r IHr | a] i n; last first.
    split => /= /eqP -> //; by apply: is_redblack_nearly_redblack.
  have Hbk : is_redblack (Bnode Black l d r) Black n ->
             is_redblack (bins (Bnode Black l d r) b i) Black n.
  rewrite {3}[Black]lock /= -lock => /andP [/andP [/prednK <- Hl] Hr].
    case: ifP => Hi.
      rewrite balanceL_Black_nearly_is_redblack //; by apply IHl.
    rewrite balanceR_Black_nearly_is_redblack //; by apply IHr.
  split; case: c => //.
  + move=> /= /andP [Hl Hr].
    case: ifP => Hi /=; [move: Hr | move: Hl] => /is_redblack_Red_Black ->;
      rewrite /= ?andbT; by [apply IHl | apply IHr].
  + move/Hbk; by apply is_redblack_nearly_redblack.
Qed.

Definition is_red D A (B : btree D A) :=
  if B is Bnode Red _ _ _ then true else false.

Lemma binsert_is_redblack B b i n :
  is_redblack B Red n ->
  is_redblack (binsert B b i) Red (n + is_red (bins B b i)).
Proof.
  move/(proj2 (bins_is_redblack _ b i _)).
  rewrite /binsert addnC.
  destruct bins => //=.
  case: c => //= /andP [Hd1 Hd2].
  by rewrite !is_redblack_Red_Black.
Qed.

Corollary binsert_is_redblack' B b i n :
  is_redblack B Red n -> exists n', is_redblack (binsert B b i) Red n'.
Proof. esplit; apply /binsert_is_redblack /H. Qed.

End insert.

Section dinsert.

Variables low high : nat.  (* (w ^ 2)./2 and (w ^ 2).*2 *)
Hypothesis Hlow : low.*2 <= high.
Hypothesis Hhigh : 1 < high.

Definition addD d1 d2 := (d1.1 + d2.1, d1.2 + d2.2).
Definition subD d1 d2 := (d1.1 - d2.1, d1.2 - d2.2).
Local Notation balance := (balance addD subD).
Local Notation balanceL := (balanceL addD subD).
Local Notation balanceR := (balanceR addD subD).
Local Notation wf_dtree_l := (wf_dtree low high).

Definition dins_leaf s b i :=
  let s' := insert1 s b i in
  if size s + 1 == high then
    let n  := size s' %/ 2 in let sl := take n s' in let sr := drop n s' in
    Bnode Red (Bleaf _ sl) (n, count_mem true sl) (Bleaf _ sr)
  else Bleaf _ s'.

Definition lt_index i (d : nat * nat) := i < fst d.
Definition right_index i (d : nat * nat) := i - fst d.
Definition insD (d : nat * nat) b := (d.1.+1, d.2+b).

Definition dins : dtree -> bool -> nat -> dtree :=
  bins addD subD dins_leaf lt_index right_index insD.
Definition dinsert : dtree -> bool -> nat -> dtree :=
  binsert addD subD dins_leaf lt_index right_index insD.

Lemma dins_leaf_is_redblack a b i : is_redblack (dins_leaf a b i) Black 0.
Proof. rewrite /dins_leaf; by case: ifP. Qed.

(* Red-blackness invariant *)
Corollary dinsert_is_redblack B b i n :
  is_redblack B Red n -> exists n', is_redblack (dinsert B b i) Red n'.
Proof. apply /binsert_is_redblack' /dins_leaf_is_redblack. Qed.

(* Correctness of balance *)

Lemma dflatten_node c l d r :
  dflatten (Bnode c l d r) = dflatten l ++ dflatten r.
Proof. by []. Qed.

Lemma balanceE c l r d : dflatten (balance c l r d) = dflatten l ++ dflatten r.
Proof.
  rewrite /balance. case: c. exact: dflatten_node.
  case: l => [[[[] lll llD llr|llA] lD [[] lrl lrD lrr|lrA]|ll lD lr]|lA] /=;
  case: r => [[[[] rll rlD rlr|rlA] rD [[] rrl rrD rrr|rrA]|rl rD rr]|rA] /=;
    try done; by rewrite !catA.
Qed.

Lemma balanceLE c l r d: dflatten (balanceL c l r d) = dflatten l ++ dflatten r.
Proof.
  rewrite /balanceL. case: c. exact: dflatten_node.
  case: l => [[[[] lll llD llr|llA] lD [[] lrl lrD lrr|lrA]|ll lD lr]|lA] //=;
    by rewrite !catA.
Qed.

Lemma balanceRE c l r d: dflatten (balanceR c l r d) = dflatten l ++ dflatten r.
Proof.
  rewrite /balanceR. case: c. exact: dflatten_node.
  case: r => [[[[] rll rlD rlr|rlA] rD [[] rrl rrD rrr|rrA]|rl rD rr]|rA] //=;
    by rewrite !catA.
Qed.

(* Correctness of dinsert *)

Definition wf_dtree' t :=
  if t is Bleaf s then size s < high else wf_dtree_l t.

Lemma wf_dtree_dtree' t : wf_dtree_l t -> wf_dtree' t.
Proof. by case: t => //= s /andP[_ ->]. Qed.

Lemma wf_dtree'_dtree t : wf_dtree' t -> wf_dtree 0 high t.
Proof.
  elim: t => //= c l IHl [n o] r IHr; repeat decompose_rewrite => /=.
  by rewrite !(IHl,IHr,wf_dtree_dtree').
Qed.

Lemma wf_dtree'_node c l d r :
  wf_dtree' (Bnode c l d r) = wf_dtree low high (Bnode c l d r). 
Proof. by []. Qed.

Lemma dins_leafE s b i :
  size s < high -> dflatten (dins_leaf s b i) = insert1 s b i.
Proof.
  rewrite /dins /dins_leaf. case: ifP => Hi Hs //.
  by rewrite dflatten_node /dflatten cat_take_drop.
Qed.

Lemma dinsE (B : dtree) b i :
  wf_dtree_l B -> dflatten (dins B b i) = insert1 (dflatten B) b i.
Proof.
  move => wf; move: B wf b i. apply: dtree_ind => //.
  + move => c l r num ones Hnum Hones _ IHl IHr /= b i.
    case: ifPn => ?.
     - by rewrite balanceLE IHl /insert1 insert_catL -?Hnum.
     - by rewrite balanceRE IHr /insert1 insert_catR -?Hnum // leqNgt.
  + move => s /andP [_] Hs b i /=.
    by rewrite dins_leafE.
Qed.

Lemma dinsertE (B : dtree) b i :
  wf_dtree' B -> dflatten (dinsert B b i) = insert1 (dflatten B) b i.
Proof.
  case: B => [c l d r | s] wf.
    rewrite /dinsert -(dinsE b i) /binsert /dins //; by case: bins.
  rewrite /dinsert /binsert /dins -dins_leafE /=; by case: dins_leaf.
Qed.

(* Well-foundedness lemmas
 * Show that dinsert always returns a well-founded tree
 *)

Lemma balanceL_wf c (l r : dtree) d :
  wf_dtree_l (Bnode c l d r) -> wf_dtree_l (balanceL c l r d).
Proof.
  case: c d => /= -[n o] /andP[Hn] /andP[Ho] /andP[wfl wfr].
    by rewrite wfl wfr Hn Ho.
  case: l wfl Hn Ho => [[[[] ? [??] ?|?] [??] [[] ? [??] ?|?] | ? [??] ?]|?] /=;
    rewrite wfr; repeat decompose_rewrite;
    by rewrite ?(size_cat,count_cat,addKn,eqxx).
Qed.

Lemma balanceR_wf c (l r : dtree) d :
   wf_dtree_l (Bnode c l d r) -> wf_dtree_l (balanceR c l r d).
Proof.
  case: c d => /= -[n o] /andP[Hn] /andP[Ho] /andP[wfl wfr].
    by rewrite wfl wfr Hn Ho.
  case: r wfr Hn Ho => [[[[] ? [??] ?|?] [??] [[] ? [??] ?|?] | ? [??] ?]|?] /=;
    rewrite wfl; repeat decompose_rewrite;
    by rewrite ?(size_cat,count_cat,addKn,eqxx).
Qed.

Lemma leq_half n : n./2 <= n.
Proof. by rewrite -{2}(odd_double_half n) -addnn addnA leq_addl. Qed.

Lemma dins_leaf_wf s b i : size s < high -> wf_dtree' (dins_leaf s b i).
Proof.
  move=> Hs.
  rewrite /dins_leaf addn1 divn2.
  case: ifP => Hsize /=.
    rewrite ?(eqxx,size_insert1,(eqP Hsize),size_drop,size_takel,leq_half) //.
    have:= half_leq Hlow; rewrite doubleK => Hlow'.
    set hhigh := high./2.
    rewrite Hlow' -(odd_double_half high) -addnn addnA addnK.
    have Hup : 0 < odd high + high./2.
      by rewrite -addn1 leq_add // (half_leq Hhigh).
    rewrite -add1n leq_add // (leq_trans Hlow' (leq_addl _ _)).
    by rewrite -addn1 leq_add // (half_leq Hhigh).
  move: Hs.
  by rewrite size_insert1 leq_eqVlt Hsize /= => ->.
Qed.

Lemma dins_wf (B : dtree) b i :
  wf_dtree low high B -> wf_dtree low high (dins B b i).
Proof.
  move => wf;  move: B wf b i.
  apply: dtree_ind =>
         [c l r num ones -> -> [wfl wfr] IHl IHr b i | s Hs b i] /=.
    case: ifP => Hi.
      apply: balanceL_wf => /=;
      by rewrite IHl wfr dinsE // size_insert1 count_insert1 eqb_id !eqxx.
    apply: balanceR_wf => /=; by rewrite IHr wfl !eqxx.
  have/andP[Hs1 Hs2]:= Hs.
  have:= dins_leaf_wf b i Hs2.
  case Hins: dins_leaf => [//|s'] /= ->.
  move: Hins; rewrite /dins_leaf.
  case: ifP => // _ [] <-.
  by rewrite size_insert1 (leq_trans Hs1).
Qed.

Lemma recolor_node_wf c c' d (l r : dtree) :
  wf_dtree' (Bnode c l d r) -> wf_dtree' (Bnode c' l d r).
Proof. by []. Qed.

Definition is_leaf (t : dtree) := if t is Bleaf _ then true else false.

Lemma dins_leaf_leaf t b i : is_leaf (dins t b i) ==> is_leaf t.
Proof.
  apply/implyP.
  case: t => //= c l [n o] r.
  case: ifP => _ /=; rewrite /balanceL /balanceR; case: c => //=;
    by case: dins => //= -[] // [[] ? ? ?|?] [n' o'] [[] ? ? ?|?].
Qed.

Lemma dinsert_wf (B : dtree) b i :
  wf_dtree' B -> wf_dtree' (dinsert B b i).
Proof.
  rewrite /dinsert /binsert -/dins => wf.
  have:= @dins_leaf_leaf B b i.
  case Hins: (dins B b i) => [c' l' [? ?] r' | s'] Hlf.
    apply (@recolor_node_wf c').
    case: B wf Hins {Hlf} => [c l [num ones] r | s] wf Hins.
      apply wf_dtree_dtree'.
      by rewrite -Hins dins_wf.
    rewrite -Hins /=.
    by apply dins_leaf_wf.
  case: B wf Hins Hlf => //= s Hs Hins b'.
  move: (dins_leaf_wf b i Hs) => /=.
  by rewrite Hins.
Qed.

(* Interaction with other operations *)

Definition dinsert_wf0 B b i wf := wf_dtree'_dtree (@dinsert_wf B b i wf).

Lemma dinsert_rank (B : dtree) b i j :
  wf_dtree' B -> drank (dinsert B b i) j =
                 rank true j (insert1 (dflatten B) b i).
Proof.
  move => wf; by rewrite -dinsertE // (@drankE 0 high) // dinsert_wf0.
Qed.

Lemma dinsert_select1 (B : dtree) b i j : wf_dtree' B ->
  dselect_1 (dinsert B b i) j = select true j (insert1 (dflatten B) b i).
Proof.
  move => wf; by rewrite -dinsertE // (@dselect_1E 0 high) // dinsert_wf0.
Qed.

Lemma dinsert_select0 (B : dtree) b i j : wf_dtree' B ->
 dselect_0 (dinsert B b i) j = select false j (insert1 (dflatten B) b i).
Proof.
  move => wf; by rewrite -dinsertE // (@dselect_0E 0 high) // dinsert_wf0.
Qed.

End dinsert.

Section set_clear.

Variables low high : nat.
Hypothesis Hlow : low.*2 <= high.
Hypothesis Hhigh : 1 < high.
Local Notation wf_dtree' := (wf_dtree' low high).

Fixpoint bset (B : dtree) i : (dtree * bool) :=
  match B with
  | Bleaf s => (Bleaf _ (bit_set s i), ~~ (nth true s i))
  | Bnode c l (num, ones) r =>
    if i < num
    then let (l', flip) := bset l i
         in  (Bnode c l' (num, ones + flip) r, flip)
    else let (r', flip) := bset r (i - num)
         in  (Bnode c l (num, ones) r', flip)
  end.

Fixpoint bclear (B : dtree) i : (dtree * bool) :=
  match B with
  | Bleaf s => (Bleaf _ (bit_clear s i), nth true s i)
  | Bnode c l (num, ones) r =>
    if i < num
    then let (l', flip) := bclear l i
         in (Bnode c l' (num, ones - flip) r, flip)
    else let (r', flip) := bclear r (i - num)
         in  (Bnode c l (num, ones) r', flip)
  end.

Definition dbitset (B : dtree) i := fst (bset B i).

Definition dbitclear (B : dtree) i := fst (bclear B i).

Lemma dbitsetE (B : dtree) i :
  wf_dtree' B -> dflatten (dbitset B i) = bit_set (dflatten B) i.
Proof.
  move=> /wf_dtree'_dtree wf; move: B wf i; rewrite /bit_set.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  rewrite update_cat -IHl -IHr /dbitset /=.
  by case: ifP => Hi; case: bset => // l' [].
Qed.

Lemma dbitclearE (B : dtree) i :
  wf_dtree' B -> dflatten (dbitclear B i) = bit_clear (dflatten B) i.
Proof.
  move=> /wf_dtree'_dtree wf; move: B wf i; rewrite /bit_clear.
  apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
  rewrite update_cat -IHl -IHr /dbitclear /=.
  by case: ifP => Hi; case: bclear => // l' [].
Qed.

Lemma size_bset (B : dtree) i : size_df (bset B i).1 = size_df B.
Proof.
  elim: B i => [c l IHl [num ones] r IHr | s] //= i; last first.
    by rewrite -size_update.
  case: ifP => Hi; [move: (IHl i) | move: (IHr (i-num))] => H;
    rewrite size_cat -H -size_cat; by case: bset.
Qed.

Lemma size_bclear (B : dtree) i : size_df (bclear B i).1 = size_df B.
Proof.
  elim: B i => [c l IHl [num ones] r IHr | s] //= i; last first.
    by rewrite -size_update.
  case: ifP => Hi; [move: (IHl i) | move: (IHr (i-num))] => H;
    rewrite size_cat -H -size_cat; by case: bclear.
Qed.

Lemma size_dbitset (B : dtree) i : size_df (dbitset B i) = size_df B.
Proof. by rewrite /dbitset size_bset. Qed.

Lemma size_dbitclear (B : dtree) i : size_df (dbitclear B i) = size_df B.
Proof. by rewrite /dbitclear size_bclear. Qed.

Lemma flip_bit_bset (B : dtree) i :
  wf_dtree low high B -> i < size_df B -> (bset B i).2 = ~~ (daccess B i).
Proof.
  move=> wf; move: B wf i.
  apply: dtree_ind; last first.
    move=> s Hs i Hi; congr negb; by apply set_nth_default.
  move=> c l r num ones Hnum Hones [wfl wfr] IHl IHr i /=.
  rewrite size_cat Hnum => Hsz.
  case: ifP => Hi.
    by rewrite -IHl; case: bset.
  rewrite -IHr; case: bset => // _ _.
  by rewrite -subSn ?leq_subLR // leqNgt Hi.
Qed.

Lemma flip_bit_bclear (B : dtree) i :
  wf_dtree low high B -> i < size_df B -> (bclear B i).2 = daccess B i.
Proof.
  move=> wf; move: B wf i.
  apply: dtree_ind; last first.
    move => s Hs i Hi; by apply set_nth_default.
  move => c l r num ones Hnum Hones [wfl wfr] IHl IHr i /=.
  rewrite size_cat Hnum => Hsz.
  case: ifP => Hi.
    by rewrite -IHl; case: bclear.
  rewrite -IHr; case: bclear => // _ _.
  by rewrite -subSn ?leq_subLR // leqNgt Hi.
Qed.

Lemma ones_dbitset (B : dtree) i :
  wf_dtree low high B -> i < size_df B ->
  ones_df (dbitset B i) = ones_df B + ~~ daccess B i.
Proof.
  rewrite /dbitset.
  move=> wf Hsize; move: B wf i Hsize.
  apply: dtree_ind => //= [ c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi
                          | s Hs i Hi ]; last by rewrite addnC -count_bit_set.
  case: ifP => Hil.
    move Hbset: (bset l i) => [l' b] /=.
    by rewrite !count_cat addnAC -IHl // Hbset.
  move Hbset: (bset r _) => [r' b] /=.
  rewrite !count_cat -addnA -IHr ?Hbset //.
  by rewrite -(ltn_add2l (size_df l)) subnKC -?size_cat // leqNgt Hil.
Qed.

Lemma flipped_count_pos (B : dtree) i :
  wf_dtree low high B -> i < size_df B -> (bclear B i).2 -> ones_df B > 0.
Proof.
  move=> wf Hsize; rewrite flip_bit_bclear // (daccessE wf) /access => H.
  by rewrite (true_count_pos _ H).
Qed.

Lemma ones_dbitclear (B : dtree) i :
  wf_dtree low high B -> i < size_df B ->
  ones_df (dbitclear B i) = ones_df B - daccess B i.
Proof.
  rewrite /dbitclear.
  move=> wf Hsize; move: B wf i Hsize.
  apply: dtree_ind => //=
    [c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi | s Hs i Hi];
    last by rewrite -count_bit_clear.
  case: ifP => Hil.
    case_eq (bclear l i) => l' b Hbclear /=.
      rewrite !count_cat [in RHS]addnC -addnBA.
      by rewrite -IHl // Hbclear addnC.
    rewrite -flip_bit_bclear // Hbclear /=.
    destruct b => //.
    by rewrite (flipped_count_pos wfl Hil) // Hbclear.
  have Hilr: i - size_df l < size_df r.
    by rewrite -(ltn_add2l (size_df l)) subnKC -?size_cat // leqNgt Hil.
  case_eq (bclear r (i - size_df l)) => r' b Hbclear /=.
    rewrite !count_cat -addnBA. by rewrite -IHr // Hbclear.
  rewrite -flip_bit_bclear // Hbclear /=.
  destruct b => //.
  by rewrite (@flipped_count_pos _ (i - size_df l)) // Hbclear.
Qed.

Lemma wf_dbitset (B : dtree) i :
  wf_dtree' B -> wf_dtree' (dbitset B i).
Proof.
  case: B => [c l d r | s] wf; last by rewrite /= size_bit_set.
  apply wf_dtree_dtree'.
  move: wf i; rewrite wf_dtree'_node; move: {c l d r} (Bnode _ _ _ _).
  apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr|s Hs] i;
    last by rewrite size_bit_set.
  rewrite /dbitset //=.
  case: ifP => Hi.
    case_eq (bset l i) => l' b Hbset /=; rewrite wfr andbT.
    move/(f_equal fst): (Hbset) => /= Hbset1.
    move/(_ i) in IHl; rewrite /dbitset Hbset1 in IHl.
    rewrite -Hbset1 size_bset.
    rewrite ?[in wf_dtree _ _ _]Hbset1 //.
    rewrite ones_dbitset // -?flip_bit_bset //.
    by rewrite Hbset !eqxx.
  case_eq (bset r (i - (size_df l))) => r' b /(f_equal fst) /= <-.
  by rewrite wfl !eqxx /= IHr.
Qed.

Lemma wf_dbitclear (B : dtree) i :
  wf_dtree' B -> wf_dtree' (dbitclear B i).
Proof.
  case: B => [c l d r | s] wf; last by rewrite /= size_bit_clear.
  apply wf_dtree_dtree'.
  move: wf i; rewrite wf_dtree'_node; move: {c l d r} (Bnode _ _ _ _).
  apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr|s Hs] i /=;
    last by rewrite size_bit_clear.
  rewrite /dbitclear //=.
  case: ifP => Hi.
    case_eq (bclear l i) => l' b Hbclear /=; rewrite wfr andbT.
    move/(f_equal fst): (Hbclear) => /= Hbclear1.
    move/(_ i) in IHl; rewrite /dbitclear Hbclear1 in IHl.
    rewrite -Hbclear1 size_bclear.
    rewrite [in wf_dtree _ _ _]Hbclear1 //.
    rewrite ones_dbitclear // -?flip_bit_bclear //;
    by rewrite Hbclear !eqxx.
  case_eq (bclear r (i - (size_df l))) => r' b /(f_equal fst) /= <-.
  by rewrite wfl !eqxx /= IHr.
Qed.

End set_clear.

Section delete.

Variables D A : Type.
Variable mkD : btree D A -> D.

Definition rbnode c l r := Bnode c l (mkD l) r.
Definition bnode l r := Bnode Black l (mkD l) r.
Definition rnode l r := Bnode Red l (mkD l) r.
Local Notation leaf a := (Bleaf _ a : btree D A).

Inductive deleted_btree: Type :=
| Stay : btree D A -> deleted_btree
| Down : btree D A -> deleted_btree.

Definition balanceL' col (l : deleted_btree) r : deleted_btree :=
  match l with
  | Stay l => Stay (rbnode col l r)
  | Down l =>
    match col, r with
    | _, Bnode Black (Bnode Red rll _ rlr) _ rr =>
      Stay (rbnode col (bnode l rll) (bnode rlr rr))
    | Red, Bnode Black (Bleaf _ as rl) _ rr
    | Red, Bnode Black (Bnode Black _ _ _ as rl) _ rr =>
      Stay (bnode (rnode l rl) rr)
    | Black, Bnode Red (Bnode Black (Bnode Black _ _ _ as rll) _ rlr) _ rr
    | Black, Bnode Red (Bnode Black (Bleaf _ as rll) _ rlr) _ rr =>
      Stay (bnode (bnode (rnode l rll) rlr) rr)
    | Black, Bnode Red (Bnode Black (Bnode Red rlll _ rllr) _ rlr) _ rr =>
      Stay (bnode (bnode l rlll) (rnode (bnode rllr rlr) rr))
    | Black, Bnode Black (Bleaf _ as rl) _ rr
    | Black, Bnode Black (Bnode Black _ _ _ as rl) _ rr =>
      Down (bnode (rnode l rl) rr)
    | _, _ => Stay (rbnode col l r)
    end
  end.
  
Definition balanceR' col l (r : deleted_btree) : deleted_btree :=
  match r with
  | Stay r => Stay (rbnode col l r)
  | Down r =>
    match col, l with
    | _, Bnode Black ll _ (Bnode Red lrl _ lrr) =>
      Stay (rbnode col (bnode ll lrl) (bnode lrr r))
    | Red, Bnode Black ll _ (Bleaf _ as lr)
    | Red, Bnode Black ll _ (Bnode Black _ _ _ as lr) =>
      Stay (bnode ll (rnode lr r))
    | Black, Bnode Red ll _ (Bnode Black lrl _ (Bnode Black _ _ _ as lrr))
    | Black, Bnode Red ll _ (Bnode Black lrl _ (Bleaf _ as lrr)) =>
      Stay (bnode ll (bnode lrl (rnode lrr r)))
    | Black, Bnode Red ll _ (Bnode Black lrl _ (Bnode Red lrrl _ lrrr)) =>
      Stay (bnode (rnode ll (bnode lrl lrrl)) (bnode lrrr r))
    | Black, Bnode Black ll _ (Bleaf _ as lr)
    | Black, Bnode Black ll _ (Bnode Black _ _ _ as lr) =>
      Down (bnode ll (rnode lr r))
    | _, _ => Stay (rbnode col l r)
    end
  end.

Variable lt_index : nat -> D -> bool.
Variable right_index : nat -> D -> nat.
Variable delete_leaf : A -> nat -> A.
Variable delete_from_leaves : color -> A -> A -> nat -> deleted_btree.

Fixpoint bdel B (i : nat) { struct B } : deleted_btree :=
  match B with
  | Bnode c (Bleaf l) d (Bleaf r) => delete_from_leaves c l r i
  | Bnode Black (Bnode Red (Bleaf ll) ld (Bleaf lr) as l) d (Bleaf r) =>
    if lt_index i d
    then balanceL' Black (bdel l i) (Bleaf _ r)
    else balanceR' Black (Bleaf _ ll)
                   (delete_from_leaves Red lr r (right_index i ld))
  | Bnode Black (Bleaf l) ld (Bnode Red (Bleaf rl) rd (Bleaf rr) as r) =>
    if lt_index (right_index i ld) rd
    then balanceL' Black (delete_from_leaves Red l rl i) (Bleaf _ rr)
    else balanceR' Black (Bleaf _ l) (bdel r (right_index i ld))
  | Bnode c l d r => 
    if lt_index i d
    then balanceL' c (bdel l i) r
    else balanceR' c l (bdel r (right_index i d))
  | Bleaf x => Stay (leaf (delete_leaf x i))
  end.

Definition is_nearly_redblack' tr c bh :=
  match tr with
  | Stay tr => is_redblack tr c bh
  | Down tr => is_redblack tr Red bh.-1
  end.

Hypothesis Hdelete_from_leaves : forall c l d r i c' n,
  is_redblack (Bnode c (Bleaf D l) d (Bleaf D r)) c' n ->
  is_nearly_redblack' (delete_from_leaves c l r i) c' n.
  
Lemma is_nearly_redblack'_Red_Black B n :
  is_nearly_redblack' B Red n -> is_nearly_redblack' B Black n.
Proof. case: B => [[]|] //= [] //. Qed.
    
Lemma balanceL'_Black_nearly_is_redblack l r n c :
  0 < n -> is_nearly_redblack' l Black n.-1 -> is_redblack r Black n.-1 ->
  is_nearly_redblack' (balanceL' Black l r) c n.
Proof.
  case: l => [l /= -> -> -> // | l Hn okl okr].
  case: c n r l okr okl Hn => [] [//|n]
    [[[[] [[] rlll ? rllr|?] ? rlr|?] ? rr| [[] rll ? rlr| ?] ? rr]|?] l //=;
  repeat decompose_rewrite; by rewrite // !is_redblack_Red_Black.
Qed.
  
Lemma balanceL'_Red_nearly_is_redblack l r n :
  is_nearly_redblack' l Red n -> is_redblack r Red n ->
  is_nearly_redblack' (balanceL' Red l r) Black n.
Proof.
  case: l => [l /= -> -> // | l okl okr].
  case: r l okr okl => [ [//|] [[] rll ? rlr| ?] ? rr | ?] l /=;
  repeat decompose_rewrite; by rewrite // !is_redblack_Red_Black.
Qed.
    
Lemma balanceR'_Black_nearly_is_redblack l r n c :
  0 < n -> is_redblack l Black n.-1 -> is_nearly_redblack' r Black n.-1 ->
  is_nearly_redblack' (balanceR' Black l r) c n.
Proof.
  case: r => [r /= -> -> -> //| //].
  case: c n l => [] [//|n] [[[[] lll ? llr|?] ?
    [[] lrl ? [[] lrrl ? lrrr|?]|?]|ll ? [[] lrl ? lrr|?]]|?] /=;
  repeat decompose_rewrite; by rewrite // !is_redblack_Red_Black. 
Qed.
  
Lemma balanceR'_Red_nearly_is_redblack l r n :
  is_redblack l Red n -> is_nearly_redblack' r Red n ->
  is_nearly_redblack' (balanceR' Red l r) Black n.
Proof.
  case: r => [r /= -> -> //| //].
  case: l => [ [//|] ll ? [[] lrl ? lrr|?] |?] r /=;
  repeat decompose_rewrite; by rewrite // !is_redblack_Red_Black. 
Qed.
  
(* This tactic is not necessary,
   but if it is removed, a proof becomes more slower. *)
Ltac close_branch d H IHl IHr :=
 rewrite /=;
 try case:ifP=>?;
 repeat (apply balanceL'_Red_nearly_is_redblack ||
         apply balanceL'_Red_nearly_is_redblack ||
         apply balanceR'_Red_nearly_is_redblack ||
         apply balanceL'_Black_nearly_is_redblack ||
         apply balanceR'_Black_nearly_is_redblack ||
         apply IHl ||
         apply IHr ||
         apply (Hdelete_from_leaves (d:=d)));
 decomp H.

Lemma bdel_is_nearly_redblack' B i n c :
  is_redblack B c n -> is_nearly_redblack' (bdel B i) c n.
Proof.
elim: B c i n => // c l IHl d r IHr p i n H //.
time (case: p c l IHl H => [] []// [[]//[[]//???|?]?[[]//???|?]|?] IHl H;
  try (by close_branch d H IHl IHr);
  case: r IHr H => [[]//[[]//???|?]?[[]//???|?]|?] IHr H;
  by close_branch d H IHl IHr).
(* 153s -> 73s by rewrite ? -> repeat apply || *)
Qed.

End delete.

Section ddelete.

Variables low high : nat.
Hypothesis Hlow : low.*2 <= high.
Hypothesis Hlow1 : low >= 1.
Let Hhigh : 1 < high.
Proof. by rewrite (leq_trans _ Hlow) // (leq_double 1 low). Qed.
Local Notation wf_dtree' := (wf_dtree' low high).
Local Notation wf_dtree_l := (wf_dtree low high).
Local Notation donesE' := (@donesE low high).
Local Notation dsizeE' := (@dsizeE low high).
Local Notation leaf a := (Bleaf _ a : dtree).
Definition mkD l := (dsize l, dones l).
Local Notation rbnode := (rbnode mkD).
Definition deleted_dtree := deleted_btree (nat * nat) (seq bool).
Local Notation balanceL' c B b := (balanceL' mkD c B b : deleted_dtree).
Local Notation balanceR' c B b := (balanceR' mkD c B b : deleted_dtree).

Definition delete_from_leaves (p : color) l r (i : nat) : deleted_dtree :=
  if i < size l
  then match low == size l, low == size r with
       | true, true =>
         Down (leaf ((rcons (delete l i) (access r 0)) ++ (delete r 0)))
       | true, false =>
         Stay (rbnode p (leaf (rcons (delete l i) (access r 0)))
                          (leaf (delete r 0)))
       | false, _ =>
         Stay (rbnode p (leaf (delete l i)) (leaf r))
       end
  else match low == size l, low == size r with
       | true, true =>
         Down (leaf (l ++ (delete r (i - (size l)))))
       | false, true =>
         Stay (rbnode p (leaf (delete l (size l).-1))
                   (leaf (access l (size l).-1 :: delete r (i - size l))))
       | _, false =>
         Stay (rbnode p (leaf l) (leaf (delete r (i - size l))))
       end.

Lemma delete_from_leaves_nearly_redblack' c l d r i c' n :
  is_redblack (Bnode c (leaf l) d (leaf r)) c' n ->
  is_nearly_redblack' (delete_from_leaves c l r i) c' n.
Proof.
  rewrite /delete_from_leaves.
  case: c c' => /= -[]; repeat case: ifP => ?; repeat decompose_rewrite => //=.
Qed.

Notation ddel := (bdel mkD lt_index right_index (@delete _) delete_from_leaves
                  : btree (nat * nat) (seq bool) -> nat -> deleted_dtree).

(* Red-blackness invariant *)
Lemma ddel_is_nearly_redblack' B i n c :
  is_redblack B c n -> is_nearly_redblack' (ddel B i) c n.
Proof.
  apply /bdel_is_nearly_redblack' /delete_from_leaves_nearly_redblack'.
Qed.

(* Forget Stay/Down *)
Definition dtree_of_deleted_dtree (B : deleted_dtree) : dtree :=
  match B with
  | Stay b => b
  | Down b => b
  end.
Coercion dtree_of_deleted_dtree : deleted_dtree >-> dtree.

Definition ddelete (B : dtree) i : dtree := (ddel B i : deleted_dtree).

Corollary ddelete_is_redblack B i n :
  is_redblack B Red n -> exists n', is_redblack (ddelete B i) Red n'.
Proof.
  rewrite /ddelete => /(ddel_is_nearly_redblack' i).
  case: ddel => B' /= rb; eexists; by apply: rb.
Qed.

(* Correctness lemmas *)

Lemma balanceL'E c (l : deleted_dtree) r :
  dflatten (balanceL' c l r) = dflatten l ++ dflatten r.
Proof. 
  move: l => [] ?; case c; case r => [] [] // [] //= [] [] [] /=; 
  intros; by rewrite //= -!catA //= -!catA.
Qed.

Lemma balanceR'E c l (r : deleted_dtree) :
  dflatten (balanceR' c l r) = dflatten l ++ dflatten r.
Proof.
  move: r => [] ?; case c; case l => //= [c'] ? ? [c''|]; 
  try case c'; try case c''; try (intros; by rewrite //= -!catA //= -!catA);
  move => ? ? [] x; first case x; intros; by rewrite //= -!catA //= -!catA.
Qed.

Lemma delete_from_leavesE c l r i :
  low <= size l < high -> low <= size r < high ->
  dflatten (delete_from_leaves c l r i) = delete (l ++ r) i.
Proof.
  rewrite /delete_from_leaves delete_cat.
  case: ifP; case: ifP => //; case: ifP => //;
    try rewrite /delete /= take0 drop1 cat0s cat_rcons -!catA.
      case r => //= /eqP -> /eqP <-; by rewrite ltn0.
    case r => //= Hlow0 _ _ _ /andP []; by rewrite leqn0 Hlow0.
  move/eqP => -> /= Hnl Hi /andP [Hl Hl'] Hr'.
  have Hl0 : 0 < size l by move: Hl; rewrite leq_eqVlt Hnl /=; case: (size l).
  rewrite /delete /= /access drop_oversize ?prednK //.
  by rewrite cats0 -cat_rcons -take_nth prednK // take_oversize.
Qed.
  
Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. case: p => //= p; by rewrite addnS !ltnS leq_subLR. Qed.

Lemma ddel_cat c l a b r i :
  wf_dtree_l (Bnode c l (a, b) r) ->
  dflatten (ddel (Bnode c l (a, b) r) i) =
  if i < a
  then dflatten (ddel l i) ++ dflatten r
  else dflatten l ++ dflatten (ddel r (i - a)).
Proof.
  rewrite /= /lt_index /right_index /=.
  time (case: ifP => Hc; case: c l r =>
      [] [[]// [??[??]?|?] [??] [??[??]?|?]|?]
      [[] [??[??]?|?] [??] [??[??]?|?]|?] wfB //;
    try case:ifP;
    rewrite ?(balanceL'E, balanceR'E, delete_cat, delete_from_leavesE,
              ltn_subLR, leq_trans Hlow1) //;
    move:wfB Hc; rewrite ?size_cat;
    do! decompose_rewrite => //=).
    (* 94s => 54s by delaying ltn_addr *)
  all: rewrite ?(subnDA, catA) //.
  by rewrite ltn_addr in H10.
Qed.

Lemma ddelE (B : dtree) i :
  wf_dtree_l B -> dflatten (ddel B i) = delete (dflatten B) i.
Proof.
  elim:B i => [c l IHl [??] r IHr|B] i wfB //.
  rewrite delete_cat.
  rewrite -IHl; last by decomp wfB.
  rewrite -IHr; last by decomp wfB.
  rewrite ddel_cat //; by decomp wfB.
Qed.

Lemma ddeleteE B i :
  wf_dtree' B -> dflatten (ddelete B i) = delete (dflatten B) i.
Proof.
  case: B => // c l d r wfB.
  rewrite -ddelE // /ddelete.
Qed.

(* Well-formedness *)

Lemma balanceL'_wf (B: deleted_dtree) b c:
  wf_dtree_l B -> wf_dtree_l b -> wf_dtree_l (balanceL' c B b).
Proof.
  case: B b => B b /= wfB wfb.
    by rewrite dsizeE' // donesE' // !eqxx wfB wfb.
  move: c b wfb => [][[][[][[]?[??]?|?][??]?|?][??][[]?[??]?|?]|?] /=;
   do !decompose_rewrite => //;
   by rewrite !(size_cat,count_cat,addnA,catA,dsizeE',donesE',eqxx,wfB).
Qed.

Lemma balanceR'_wf (B: deleted_dtree) b c:
  wf_dtree_l B -> wf_dtree_l b -> wf_dtree_l (balanceR' c b B).
Proof.
  case: B b => B b /= wfB wfb.
    by rewrite dsizeE' // donesE' // !eqxx wfB wfb.
  move: c b wfb => [][[][[]?[??]?|?][??][[]?[??][[]?[??]?|?]|?]|?] /=;
   do! decompose_rewrite => //;
   by rewrite !(size_cat,count_cat,addnA,catA,dsizeE',donesE',eqxx,wfB).
Qed.

Lemma leq_predr (m n : nat) :
  (m == n) = false -> m <= n -> m <= n.-1.
Proof. rewrite leq_eqVlt => -> /= lo; by rewrite -ltnS (ltn_predK lo). Qed.

Lemma delete_from_leaves_wf l r i c:
  i < size l + size r ->
  low <= size l < high ->
  low <= size r < high ->
  wf_dtree_l (delete_from_leaves c l r i).
Proof.
  move=> sc /andP [wll wlh] /andP [wrl wrh].
  have szl: 0 < size l by apply (leq_trans Hlow1).
  have szr: 0 < size r by apply (leq_trans Hlow1).
  have szlp: (size l).-1 < size l by rewrite prednK // subnn.
  have szrp: (size r).-1 < size r by rewrite prednK // subnn.
  rewrite /delete_from_leaves; do! case: ifP; move=>rc lc /=; try (move=> Hi);
  rewrite ?(size_cat,size_rcons,size_delete,eqxx) //=;
  rewrite ?(prednK,wll,wlh,wrl,wrh) // -?(eqP rc,eqP lc);
  try (by rewrite leq_addr (leq_trans _ Hlow)// -addnn ltn_add2l prednK);
  rewrite ?leq_predr // ?ltn_subLR //; try by rewrite ltnW.
  by rewrite {1}(eqP lc) (eqP rc).
Qed.

Lemma dsize_gt0 (B: dtree) : wf_dtree_l B -> size_df B > 0.
Proof.
move: B; apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr|s wf] /=.
  by rewrite size_cat ltn_addr.
rewrite (leq_trans Hlow1); by decomp wf.
Qed.

Lemma ddel_wf (B : dtree) n i :
  0 < n ->
  i < dsize B ->
  is_redblack B Black n ->
  wf_dtree_l B ->
  wf_dtree_l (ddel B i).
Proof.
  move => Hn Hi rbB wfB; rewrite dsizeE' // in Hi; move: Hn Hi rbB wfB.
  rewrite /= /lt_index /right_index /=.
  elim: B n i => [[] l IHl [??] r IHr|?] n i Hn Hi rbB wfB /=;
    last by move/eqP: rbB Hn => /= ->.
  + case: ifP => Hc;
    case: l r Hi rbB IHl IHr wfB =>
        [[]?[??]?|?] [[]?[??]?|?]// Hi rbB IHl IHr wfB;
    rewrite ?(balanceL'_wf, balanceR'_wf,
              IHl n, IHr n, delete_from_leaves_wf, ltn_subLR) //;
    move: rbB wfB Hi Hc;
    do! (decompose_rewrite; rewrite /= ?size_cat) => //;
    rewrite ?(ltn_addr, dsize_gt0, leq_trans Hlow1) //=.
  + case: n Hn rbB => [//|[|n]] Hn rbB.
  * case: l r Hi rbB IHl IHr wfB =>
        [[] [[]//|?] [??] [[]//|?]|?] [[] [[]//|?] [??] [[]|?]|?] //=
        Hi rbB IHl IHr wfB;
      try case: ifP => Hc;
      rewrite ?(balanceL'_wf, balanceR'_wf, delete_from_leaves_wf) //;
      try move: Hc; move: wfB rbB Hi;
      do! (decompose_rewrite; rewrite /= ?size_cat //).
    - by rewrite ltn_subLR // ltn_addr // (leq_trans Hlow1).
    - by rewrite ltn_subLR ?addnA // ltn_addr // (leq_trans Hlow1).
    - by rewrite -ltn_subLR // (leq_trans Hlow1).
    - by rewrite ltn_subLR // ltn_addr // (leq_trans Hlow1).
  * time (case:l r Hi rbB IHl IHr wfB =>
        [[] ll [??] lr|?] [[]?[??]?|?] Hi rbB IHl IHr wfB;
      last rewrite delete_from_leaves_wf //;
      case: ifP => Hc //;
      try case: ll lr IHl rbB wfB Hi => [[]???|?] [[]???|?] // IHl rbB wfB Hi;
      rewrite ?(balanceL'_wf, balanceR'_wf,
                IHl n.+1, IHr n.+1, delete_from_leaves_wf, ltn_subLR) //;
      move: rbB wfB Hi Hc;
      do! (decompose_rewrite; rewrite //= ?size_cat); (* 66s => 59s by //= *)
      by rewrite ?(ltn_addr, dsize_gt0, leq_trans Hlow1)).
Qed.

Lemma ddelete_wf (B : dtree) n i :
  is_redblack B Black n ->
  i < size_df B ->
  wf_dtree' B ->
  wf_dtree' (ddelete B i).
Proof.
  case: n => [|n].
    case: B => [[]// [[]//???|s1] [n1 o1] [[]//???|s2]|s] //=.
      rewrite size_cat => _ Hi wf.
      apply /wf_dtree_dtree' /delete_from_leaves_wf => //; by decomp wf.
    move=> _ Hi Hs; rewrite size_delete //.
    by rewrite (ltn_predK Hi) ltnW.
  case: B => // c l [s o] r rb Hi wf.
  apply /wf_dtree_dtree' /(@ddel_wf _ n.+1); by rewrite // dsizeE'.
Qed.

End ddelete.

Section example.
Definition t : dtree :=
  Bnode Black
        (Bleaf _ [:: true; false; false])
        (3, 1)
        (Bnode Red
               (Bleaf _ [:: true; false; true])
               (3, 2)
               (Bleaf _ [:: true; true; true; true])).
Lemma drank_t : drank t 10 == 7. Proof. by []. Qed.
Lemma dselect1_t : dselect_1 t 7 == 10. Proof. by []. Qed.
Lemma dselect0_t : dselect_0 t 3 == 5. Proof. by []. Qed.
Lemma dinsert_t :
  dinsert 5 (* upper bound *) t false 9 ==
  Bnode Black
        (Bnode Black
               (Bleaf _ [:: true; false; false])
               (3, 1)
               (Bleaf _ [:: true; false; true]))
        (6, 3)
        (Bnode Black
               (Bleaf _ [:: true; true])
               (2, 2)
               (Bleaf _ [:: true; false; true])).
Proof. by []. Qed.
Lemma ddelete_t :
  ddelete 3 (* lower bound *) t 2 ==
  Bnode Black
        (Bleaf _ [:: true; false; true; false; true])
        (5, 3)
        (Bleaf _ [:: true; true; true; true]).
Proof. by []. Qed.
End example.
