From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete set_clear Recdef.

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
  move: t1 t2; elim => [? l1 lH1 ? r1 rH1|?]; elim => [? l2 lH2 ? r2 rH2 H|?] //;
  last by move/eqP => /= ->.
  move/andP: H; case; move/andP; case; move/andP; case; move/eqP => ->; move/eqP => -> H1 H2.
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
  | Bnode _ l _ r => dsize l + dsize r
  | Bleaf s => size s
  end.

Fixpoint dones (B : dtree) :=
  match B with
  | Bnode _ l _ r => dones l + dones r
  | Bleaf s => count_mem true s
  end.


Definition access (s : seq bool) i := nth false s i.

Variables low high : nat.  (* (w ^ 2)./2 and (w ^ 2).*2 *)

Fixpoint wf_dtree (B : dtree) :=
  match B with
  | Bnode _ l (num, ones) r =>
    [&& num == size (dflatten l),
        ones == count_mem true (dflatten l),
        wf_dtree l & wf_dtree r]
  | Bleaf arr =>
    low <= size arr < high
  end.

Lemma dtree_ind (P : dtree -> Prop) :
  (forall c (l r : dtree) num ones,
      num = size (dflatten l) -> ones = count_mem true (dflatten l) ->
      wf_dtree l /\ wf_dtree r ->
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

Lemma dsizeE (B : dtree) : wf_dtree B -> dsize B = size (dflatten B).
Proof.
  move=> wf; move: B wf.
  apply: dtree_ind => // c l r num ones Hnum Hones _ IHl IHr /=.
  by rewrite IHl IHr size_cat.
Qed.

Lemma donesE (B : dtree) : wf_dtree B -> dones B = count_mem true (dflatten B).
Proof.
  move=> wf; move: B wf.
  apply: dtree_ind => // c l r num ones Hnum Hones _ IHl IHr /=.
  by rewrite IHl IHr count_cat.
Qed.

Corollary drank_all (B : dtree) :
  wf_dtree B -> drank B (dsize B) = (count_mem true) (dflatten B).
Proof. move => wf. by rewrite drankE // /rank dsizeE // take_size. Qed.

Definition drank_size B := drank B (dsize B).

End dtree.


Section insert.
Variables D A : Type.
Variable mkD : btree D A -> D.

Definition balance col (l r : btree D A) : btree D A :=
  match col with
  | Red => Bnode Red l (mkD l) r
  | Black => match l, r with
             | Bnode Red (Bnode Red a _ b) _ c, d
             | Bnode Red a _ (Bnode Red b _ c), d
             | a, Bnode Red (Bnode Red b _ c) _ d
             | a, Bnode Red b _ (Bnode Red c _ d) =>
               let l := Bnode Black a (mkD a) b in
               Bnode Red l (mkD l) (Bnode Black c (mkD c) d)
             | _, _ => Bnode Black l (mkD l) r
             end
  end.

Definition balanceL col (l r : btree D A) : btree D A :=
  match col with
  | Red => Bnode Red l (mkD l) r
  | Black => match l with
             | Bnode Red (Bnode Red a _ b) _ c
             | Bnode Red a _ (Bnode Red b _ c) =>
               let l := Bnode Black a (mkD a) b in
               Bnode Red l (mkD l) (Bnode Black c (mkD c) r)
             | _ => Bnode Black l (mkD l) r
             end
  end.

Definition balanceR col (l r : btree D A) : btree D A :=
  match col with
  | Red => Bnode Red l (mkD l) r
  | Black => match r with
             | Bnode Red (Bnode Red b _ c) _ d
             | Bnode Red b _ (Bnode Red c _ d) =>
               let lb := Bnode Black l (mkD l) b in
               Bnode Red lb (mkD lb) (Bnode Black c (mkD c) d)
             | _ => Bnode Black l (mkD l) r
             end
  end.

Variable bins_leaf : A -> bool -> nat -> btree D A.
Variable lt_index : nat -> D -> bool.
Variable update_index : nat -> D -> nat.

Fixpoint bins (B : btree D A) b i : btree D A :=
  match B with
  | Bleaf s => bins_leaf s b i
  | Bnode c l d r =>
      if lt_index i d
      then balanceL c (bins l b i) r
      else balanceR c l (bins r b (update_index i d))
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

Lemma balanceL_Black_nearly_is_redblack l r n :
  nearly_redblack l n -> is_redblack r Black n ->
  is_redblack (balanceL Black l r) Black n.+1.
Proof.
  case: l => [[[[] lll ? llr|?] ? [[] lrl ? lrr|?]|ll ? lr]|?] /=;
    repeat decompose_rewrite => //;
    by rewrite !is_redblack_Red_Black -?(eqP H1).
Qed.

Lemma balanceR_Black_nearly_is_redblack l r n :
  nearly_redblack r n -> is_redblack l Black n ->
  is_redblack (balanceR Black l r) Black n.+1.
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

Lemma binsert_is_nearly_redblack' B b i n :
  is_redblack B Red n ->
  is_redblack (binsert B b i) Red (n + is_red (bins B b i)).
Proof.
  move/(proj2 (bins_is_redblack _ b i _)).
  rewrite /binsert addnC.
  destruct bins => //=.
  case: c => //= /andP [Hd1 Hd2].
  by rewrite !is_redblack_Red_Black.
Qed.

Lemma binsert_is_redblack B b i n :
  is_redblack B Red n -> exists n', is_redblack (binsert B b i) Red n'.
Proof. esplit; apply /binsert_is_nearly_redblack' /H. Qed.

End insert.

Section balanceE.
(* Correctness lemmas *)
Variables low high : nat.  (* (w ^ 2)./2 and (w ^ 2).*2 *)
Definition mkD l := (dsize l, dones l).
Local Notation balance := (balance mkD).
Local Notation balanceL := (balanceL mkD).
Local Notation balanceR := (balanceR mkD).
Local Notation wf_dtree := (wf_dtree low high).
Local Notation donesE := (@donesE low high).
Local Notation dsizeE := (@dsizeE low high).

Lemma dflatten_node c l d r :
  dflatten (Bnode c l d r) = dflatten l ++ dflatten r.
Proof. by []. Qed.

Lemma balanceE c l r : dflatten (balance c l r) = dflatten l ++ dflatten r.
Proof.
  rewrite /balance. case: c. exact: dflatten_node.
  case: l => [[[[] lll llD llr|llA] lD [[] lrl lrD lrr|lrA]|ll lD lr]|lA] /=;
  case: r => [[[[] rll rlD rlr|rlA] rD [[] rrl rrD rrr|rrA]|rl rD rr]|rA] /=;
    try done; by rewrite !catA.
Qed.

Lemma balanceLE c l r : dflatten (balanceL c l r) = dflatten l ++ dflatten r.
Proof.
  rewrite /balanceL. case: c. exact: dflatten_node.
  case: l => [[[[] lll llD llr|llA] lD [[] lrl lrD lrr|lrA]|ll lD lr]|lA] //=;
    by rewrite !catA.
Qed.

Lemma balanceRE c l r : dflatten (balanceR c l r) = dflatten l ++ dflatten r.
Proof.
  rewrite /balanceR. case: c. exact: dflatten_node.
  case: r => [[[[] rll rlD rlr|rlA] rD [[] rrl rrD rrr|rrA]|rl rD rr]|rA] //=;
    by rewrite !catA.
Qed.

(* Well-foundedness lemmas
 * Show that dinsert always returns a well-founded tree
 *)

Lemma balanceL_wf c (l r : dtree) :
  wf_dtree l -> wf_dtree r -> wf_dtree (balanceL c l r).
Proof.
  case: c => /= wfl wfr.
    by rewrite wfl wfr !(dsizeE,donesE,eqxx).
  case: l wfl => [[[[] ? [??] ?|?] [??] [[] ? [??] ?|?] | ? [??] ?]|?] /=;
    rewrite wfr; repeat decompose_rewrite;
    by rewrite ?(dsizeE,donesE,size_cat,count_cat,eqxx).
Qed.

Lemma balanceR_wf c (l r : dtree) :
  wf_dtree l -> wf_dtree r -> wf_dtree (balanceR c l r).
Proof.
  case: c => /= wfl wfr.
    by rewrite wfl wfr ?(dsizeE,donesE,eqxx).
  case: r wfr => [[[[] ? [??] ?|?] [??] [[] ? [??] ?|?] | ? [??] ?] | ?] /=;
    rewrite wfl; repeat decompose_rewrite;
    by rewrite ?(dsizeE,donesE,size_cat,count_cat,eqxx).
Qed.
End balanceE.

Section dinsert.

Variables low high : nat.  (* (w ^ 2)./2 and (w ^ 2).*2 *)
Hypothesis Hlow : low.*2 <= high.
Hypothesis Hhigh : 1 < high.

Definition dins_leaf s b i :=
  let s' := insert1 s b i in
  if size s + 1 == high
  then let n  := (size s') %/ 2 in
       let sl := take n s' in
       let sr := drop n s' in
       Bnode Red (Bleaf _ sl) (size sl, count_mem true sl) (Bleaf _ sr)
  else Bleaf _ s'.

Definition lt_index i (d : nat * nat) := i < fst d.
Definition update_index i (d : nat * nat) := i - fst d.

Definition dins : dtree -> bool -> nat -> dtree :=
  bins mkD dins_leaf lt_index update_index.
Definition dinsert : dtree -> bool -> nat -> dtree :=
  binsert mkD dins_leaf lt_index update_index.

Local Notation wf_dtree_l := (wf_dtree low high).
Local Notation donesE := (@donesE low high).
Local Notation dsizeE := (@dsizeE low high).
Definition wf_dtree' t :=
  if t is Bleaf s then size s < high else wf_dtree low high t.

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
    case: ifP => Hi. by apply: balanceL_wf.
    by apply: balanceR_wf.
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

Definition dinsert_wf0 B b i wf := wf_dtree'_dtree (@dinsert_wf B b i wf).

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

  Lemma dsize_bset (B : dtree) i : dsize ((bset B i).1) = dsize B.
  Proof.
    elim: B i => [c l IHl [num ones] r IHr | s] //= i; last first.
      by rewrite -size_update.
    case: ifP => Hi.
      rewrite -(IHl i); by case: bset => ? [].
    rewrite -(IHr (i-num)); by case: bset => ? [].
  Qed.

  Lemma dsize_bclear (B : dtree) i : dsize ((bclear B i).1) = dsize B.
  Proof.
    elim: B i => [c l IHl [num ones] r IHr | s] //= i; last first.
      by rewrite -size_update.
    case: ifP => Hi.
      rewrite -(IHl i); by case: bclear => ? [].
    rewrite -(IHr (i-num)); by case: bclear => ? [].
  Qed.

  Lemma dsize_dbitset (B : dtree) i : dsize (dbitset B i) = dsize B.
  Proof. by rewrite /dbitset dsize_bset. Qed.

  Lemma dsize_dbitclear (B : dtree) i : dsize (dbitclear B i) = dsize B.
  Proof. by rewrite /dbitclear dsize_bclear. Qed.

  Lemma flip_bit_bset (B : dtree) i :
    wf_dtree low high B -> i < dsize B -> (bset B i).2 = ~~ (daccess B i).
  Proof.
    move=> wf; move: B wf i.
    apply: dtree_ind; last first.
      move=> s Hs i Hi; congr negb; by apply set_nth_default.
    move=> c l r num ones Hnum Hones [wfl wfr] IHl IHr i /= IHsize.
    rewrite Hnum -(dsizeE wfl) //.
    case: ifP => Hi.
      by rewrite -IHl; case: bset.
    rewrite -IHr; case: bset => // _ _.
    by rewrite -subSn ?leq_subLR // leqNgt Hi.
  Qed.

  Lemma flip_bit_bclear (B : dtree) i :
    wf_dtree low high B -> i < dsize B -> (bclear B i).2 = daccess B i.
  Proof.
    move=> wf; move: B wf i.
    apply: dtree_ind; last first.
      move => s Hs i Hi; by apply set_nth_default.
    move => c l r num ones Hnum Hones [wfl wfr] IHl IHr i /= IHsize.
    rewrite Hnum -(dsizeE wfl) //.
    case: ifP => Hi.
      by rewrite -IHl; case: bclear.
    rewrite -IHr; case: bclear => // _ _.
    by rewrite -subSn ?leq_subLR // leqNgt Hi.
  Qed.

  Lemma dones_dbitset (B : dtree) i :
    wf_dtree low high B -> i < dsize B ->
    dones (dbitset B i) = dones B + ~~ daccess B i.
  Proof.
    rewrite /dbitset.
    move=> wf Hsize; move: B wf i Hsize.
    apply: dtree_ind => //= [ c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi
                            | s Hs i Hi ]; last by rewrite addnC -count_bit_set.
    rewrite -(dsizeE wfl).
    case: ifP => Hil.
      move Hbset: (bset l i) => [l' b] /=.
      by rewrite addnAC -IHl // Hbset.
    move Hbset: (bset r (i - dsize l)) => [r' b] /=.
    rewrite -addnA -IHr ?Hbset //.
    by rewrite -(ltn_add2l (dsize l)) subnKC // leqNgt Hil.
  Qed.

  Lemma flipped_count_pos (B : dtree) i :
    wf_dtree low high B -> i < dsize B -> (bclear B i).2 -> dones B > 0.
  Proof.
    move=> wf Hsize; rewrite flip_bit_bclear // (daccessE wf) /access => H.
    by rewrite (donesE wf) (true_count_pos _ H) // -(dsizeE wf).
  Qed.

  Lemma dones_dbitclear (B : dtree) i :
    wf_dtree low high B -> i < dsize B ->
    dones (dbitclear B i) = dones B - daccess B i.
  Proof.
    rewrite /dbitclear.
    move=> wf Hsize; move: B wf i Hsize.
    apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi | s Hs i Hi].
    rewrite -(dsizeE wfl) //.
    case: ifP => Hil.
    case_eq (bclear l i) => l' b Hbclear /=.
    rewrite [in RHS]addnC -addnBA. by rewrite -IHl // Hbclear addnC.
    rewrite -flip_bit_bclear // Hbclear /=.
    destruct b => //.
    by rewrite (flipped_count_pos wfl Hil) // Hbclear.
    have Hilr: i - dsize l < dsize r.
    by rewrite -(ltn_add2l (dsize l)) subnKC // leqNgt Hil.
    case_eq (bclear r (i - dsize l)) => r' b Hbclear /=.
    rewrite -addnBA. by rewrite -IHr // Hbclear.
    rewrite -flip_bit_bclear // Hbclear /=.
    destruct b => //.
    by rewrite (@flipped_count_pos _ (i - dsize l)) // Hbclear.
    by rewrite -count_bit_clear.
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
      rewrite -!(@dsizeE low high) // -Hbset1 dsize_bset.
      rewrite -!(@donesE low high) // ?[in wf_dtree _ _ _]Hbset1 //.
      rewrite dones_dbitset // -?flip_bit_bset // ?(@dsizeE low high) //.
      by rewrite Hbset !eqxx.
    case_eq (bset r (i - (size (dflatten l)))) => r' b /(f_equal fst) /= <-.
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
      rewrite -!(@dsizeE low high) // -Hbclear1 dsize_bclear.
      rewrite -!(@donesE low high) // [in wf_dtree _ _ _]Hbclear1 //.
      rewrite dones_dbitclear // -?flip_bit_bclear //;
      by rewrite ?(@dsizeE low high) // Hbclear !eqxx.
    case_eq (bclear r (i - (size (dflatten l)))) => r' b /(f_equal fst) /= <-.
    by rewrite wfl !eqxx /= IHr.
  Qed.

End set_clear.

Section delete.

Variables D A : Type.
Variable mkD : btree D A -> D.

Definition rbnode c l r := Bnode c l (mkD l) r.
Definition bnode l r := Bnode Black l (mkD l) r.
Definition rnode l r := Bnode Red l (mkD l) r.
Definition leaf a : btree D A := Bleaf _ a.

Inductive deleted_btree: Type :=
| Stay : btree D A -> deleted_btree
| Down : btree D A -> deleted_btree.

Definition balanceL' col (l : deleted_btree) r : deleted_btree :=
  match l with
  | Stay l => Stay (rbnode col l r)
  | Down l =>
    match col,r with
    | _, Bnode Black (Bnode Red rll _ rlr) _ rr =>
      Stay (rbnode col (bnode l rll) (bnode rlr rr))
    | Red, Bnode Black (Bleaf _ as rl) _ rr
    | Red, Bnode Black (Bnode Black _ _ _ as rl) _ rr =>
      Stay (bnode (rnode l rl) rr)
    | Black,Bnode Red (Bnode Black (Bnode Black _ _ _ as rll) _ rlr) _ rr
    | Black,Bnode Red (Bnode Black (Bleaf _ as rll) _ rlr) _ rr =>
      Stay (bnode (bnode (rnode l rll) rlr) rr)
    | Black,Bnode Red (Bnode Black (Bnode Red rlll _ rllr) _ rlr) _ rr =>
      Stay (bnode (bnode l rlll) (rnode (bnode rllr rlr) rr))
    | Black,Bnode Black (Bleaf _ as rl) _ rr 
    | Black,Bnode Black (Bnode Black _ _ _ as rl) _ rr =>
      Down (bnode (rnode l rl) rr)
    (* absurd case *)
    | _,_ => Stay (rbnode col l r)
    end
  end.
  
Definition balanceR' col l (r : deleted_btree) : deleted_btree :=
  match r with
  | Stay r => Stay (rbnode col l r)
  | Down r =>
    match col,l with
    | _, Bnode Black ll _ (Bnode Red lrl _ lrr) =>
      Stay (rbnode col (bnode ll lrl) (bnode lrr r))
    | Red,Bnode Black ll _ (Bleaf _ as lr)
    | Red,Bnode Black ll _ (Bnode Black _ _ _ as lr) =>
      Stay (bnode ll (rnode lr r))
    | Black,Bnode Red ll _ (Bnode Black lrl _ (Bnode Black _ _ _ as lrr))
    | Black,Bnode Red ll _ (Bnode Black lrl _ (Bleaf _ as lrr)) =>
      Stay (bnode ll (bnode lrl (rnode lrr r)))
    | Black,Bnode Red ll _ (Bnode Black lrl _ (Bnode Red lrrl _ lrrr)) =>
      Stay (bnode (rnode ll (bnode lrl lrrl)) (bnode lrrr r))
    | Black,Bnode Black ll _ (Bleaf _ as lr)
    | Black,Bnode Black ll _ (Bnode Black _ _ _ as lr) =>
      Down (bnode ll (rnode lr r))
    (* absurd case *)
    | _,_ => Stay (rbnode col l r)
    end
  end.

Fixpoint height_of_btree (B : btree D A) :=
  match B with
  | Bnode Black l _ r => (maxn (height_of_btree l) (height_of_btree r)).+2
  | Bnode Red l _ r => (maxn (height_of_btree l) (height_of_btree r)).+1
  | Bleaf _ => 0
  end.

Lemma hc_pcl l r c d :
  height_of_btree l < height_of_btree (Bnode c l d r).
Proof.
  case c; rewrite /= -!maxnSS leq_max ltnS; [rewrite leqnn //|rewrite ltnW //].
Qed.

Lemma hc_pcr l r c d :
  height_of_btree r < height_of_btree (Bnode c l d r).
Proof.
  case c; rewrite /= -!maxnSS leq_max ltnS;
    [ rewrite leqnn orbT // | apply/orP; right; rewrite ltnW // ]. 
Qed.

Lemma hc_pcl' {lr ll r d p} :
  height_of_btree (rnode lr r) <
    height_of_btree (Bnode Black (Bnode Red ll p lr) d r).
Proof.
  rewrite /= -!maxnSS -maxnA !leq_max !/maxn; case: ifP => H;
    [ rewrite ltnSn !orbT // | rewrite [ _.+1 < (_ lr).+3]ltnW // orbT // ]. 
Qed.

Lemma hc_pcr' l rl rr d p :
  height_of_btree (rnode l rl) <
    height_of_btree (Bnode Black l d (Bnode Red rl p rr)).
Proof.
  rewrite /= -!maxnSS maxnA !leq_max !/maxn; case: ifP => H;
    [ rewrite [ _.+1 < (_ rl).+3]ltnW // orbT // | rewrite ltnSn // ]. 
Qed.
  
Lemma hc_pcr'' {ll lr rl rr lc l' dr}:
  height_of_btree (rnode (rbnode lc ll lr) (bnode rl rr)) <
  height_of_btree (bnode (rnode (leaf l') (rbnode lc ll lr)) (Bnode Black rl dr rr)).
Proof.
  move: lc => /= []; rewrite max0n !maxnSS /= /leq !subSS subn_eq0;
    rewrite /= -!maxnSS maxnA !leq_max !/maxn;
  repeat case: ifP;
  rewrite !(leqnn,leqnSn) //=;
  by (intros; rewrite !orbT).
Qed.

Variable lt_index : nat -> D -> bool.
Variable update_index : nat -> D -> nat.
Variable deleteA : A -> nat -> A.
Variable delete_leaves : color -> A -> A -> nat -> deleted_btree.

Function bdel B (i : nat) { measure height_of_btree B } : deleted_btree :=
  match B with
  | Bnode Black (Bleaf l) d (Bleaf r) => delete_leaves Black l r i
  | Bnode Red (Bleaf l) d (Bleaf r) => delete_leaves Red l r i
  | Bnode Black (Bnode Red (Bleaf ll) ld (Bleaf lr)) d (Bleaf r) => 
    if lt_index i d
    then balanceL' Black (delete_leaves Red ll lr i) (Bleaf _ r)
    else balanceR' Black (Bleaf _ ll)
                   (delete_leaves Red lr r (update_index i ld))
  | Bnode Black (Bleaf l) ld (Bnode Red (Bleaf rl) rd (Bleaf rr)) => 
    if lt_index (update_index i ld) rd
    then balanceL' Black (delete_leaves Red l rl i) (Bleaf _ rr)
    else balanceR' Black (Bleaf _ l)
                   (delete_leaves Red rl rr (update_index i ld))
  | Bnode Black (Bnode Black ll ld lr) d (Bnode Red rl rd rr) =>
    let l := Bnode Black ll ld lr in
    let r := Bnode Red rl rd rr in
    if lt_index i d
    then balanceL' Black (bdel (rnode l rl) i) rr
    else balanceR' Black l (bdel r (update_index i d))
  | Bnode Black (Bnode Red ll ld lr) d (Bnode Black rl rd rr) =>
    let l := Bnode Red ll ld lr in
    let r := Bnode Black rl rd rr in
    if lt_index i d
    then balanceL' Black (bdel l i) r
    else balanceR' Black ll (bdel (rnode lr r) (update_index i ld))
  | Bnode c l d r => 
    if lt_index i d
    then balanceL' c (bdel l i) r
    else balanceR' c l (bdel r (update_index i d))
  (* absurd case *)
  | Bleaf x =>  Stay (leaf (deleteA x i))
  end.

  all: intros; subst B; apply/leP; 
  try (apply/eqP; rewrite /= subSS; apply/eqP; try (by apply leq_maxl); by apply leq_maxr); 
  try (apply hc_pcl); try (apply hc_pcr).
  apply hc_pcl'.
  apply hc_pcr''.
  apply hc_pcr'.
Defined.

Definition is_nearly_redblack' tr c bh :=
  match tr with
  | Stay tr => is_redblack tr c bh
  | Down tr => is_redblack tr Red bh.-1
  end.

Hypothesis Hdelete_leaves : forall c l d r i c' n,
  is_redblack (Bnode c (Bleaf D l) d (Bleaf D r)) c' n ->
  is_nearly_redblack' (delete_leaves c l r i) c' n.
  
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
  
Ltac solveL' IHd ok :=
  rewrite balanceL'_Black_nearly_is_redblack // ?IHd //; decomp ok.
Ltac solveR' IHd ok :=
  rewrite balanceR'_Black_nearly_is_redblack // ?IHd //; decomp ok.
Ltac splitL' t y IHd ok :=
  case: t => [[] ? ? ?|?] // in y IHd ok *; try by solveL' IHd ok.
Ltac splitR' t y IHd ok :=
  case: t => [[] ? ? ?|?] // in y IHd ok *; try by solveR' IHd ok.
Ltac decomp_ifP ok :=
  repeat case: ifP => ?; decomp ok.

Lemma ddel_is_nearly_redblack' B i n c :
  0 < n -> is_redblack B c n -> is_nearly_redblack' (bdel B i) c n.
Proof.
move: n c; functional induction (bdel B i) => n c' H //.
+ apply Hdelete_leaves.
+ apply Hdelete_leaves.
+ move=> Hrb. 
  rewrite balanceL'_Black_nearly_is_redblack // ?(Hdelete_leaves (d:=ld));
    by decomp_ifP Hrb.
+ move=> Hrb. 
  rewrite balanceR'_Black_nearly_is_redblack // ?(Hdelete_leaves (d:=ld));
    by decomp_ifP Hrb.
+ move=> Hrb. 
  rewrite balanceL'_Black_nearly_is_redblack // ?(Hdelete_leaves (d:=ld));
    by decomp_ifP Hrb.
+ move=> Hrb. 
  rewrite balanceR'_Black_nearly_is_redblack // ?(Hdelete_leaves (d:=ld));
    by decomp_ifP Hrb.
+ move=> ok; solveL' IHd ok => //.
  by apply is_redblack_Red_Black.
+ move=> ok; by solveR' IHd ok.
+ move=> ok; by solveL' IHd ok.
+ move=> ok; solveR' IHd ok => //.
  by apply is_redblack_Red_Black.
+ move: c c' l r y IHd =>
    [] [] // [[] ll ld lr |?] [[] // rl rd rr|?] //= y IHd;
  first (by rewrite !andbF);
  try (case/andP => C /eqP H'; case/andP: C; by rewrite H' ltnn /=);
  move => ok;
  first (by rewrite balanceL'_Red_nearly_is_redblack // ?IHd //; decomp ok);
  splitL' ll y IHd ok;
  splitL' lr y IHd ok;
  apply balanceL'_Black_nearly_is_redblack => //;
  try apply (Hdelete_leaves (d:=ld)); by decomp ok.
+ move: c c' l r y IHd =>
    [] [] // [[] ll ld lr |?] [[] // rl rd rr|?] //= y IHd;
  try (by rewrite !andbF);
  try (case/andP => /eqP ->; by rewrite ltnn /=);
  move => ok;
  first (by rewrite balanceR'_Red_nearly_is_redblack // ?IHd //; decomp ok);
  splitR' rl y IHd ok;
  splitR' rr y IHd ok;
  apply balanceR'_Black_nearly_is_redblack => //;
  try apply (Hdelete_leaves (d:=rd)); by decomp ok.
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
Definition deleted_dtree := deleted_btree (nat * nat) (seq bool).

Definition delete_leaves (p : color) l r (i : nat) : deleted_dtree :=
  if i < size l
  then match low == size l, low == size r with
       | true,true =>
         Down (leaf _ ((rcons (delete l i) (access r 0)) ++ (delete r 0)))
       | true,false => 
         Stay (rbnode mkD p (leaf _ (rcons (delete l i) (access r 0)))
                          (leaf _ (delete r 0)))
       | false,_ => 
         Stay (rbnode mkD p (leaf _ (delete l i)) (leaf _ r))
       end
  else match low == size l, low == size r with
       | true,true =>
         Down (leaf _ (l ++ (delete r (i - (size l)))))
       | false,true => 
         Stay (rbnode mkD p (leaf _ (delete l (size l).-1))
                   (leaf _ (access l (size l).-1 :: delete r (i - size l))))
       | _,false => 
         Stay (rbnode mkD p (leaf _ l) (leaf _ (delete r (i - size l))))
       end.

Lemma delete_leaves_nearly_redblack' c l d r i c' n :
  is_redblack (Bnode c (Bleaf (nat*nat) l) d (Bleaf _ r)) c' n ->
  is_nearly_redblack' (delete_leaves c l r i) c' n.
Proof.
  rewrite /delete_leaves.
  case: c c' => /= -[]; repeat case: ifP => ?; repeat decompose_rewrite => //=.
Qed.

Notation ddel := (bdel mkD lt_index update_index (@delete _) delete_leaves).

Lemma ddel0E s o l r i :
  ddel (Bnode Red (Bleaf _ l) (s,o) (Bleaf _ r)) i = delete_leaves Red l r i.
Proof.
  move Heq : (Bnode Red _ _ _) => B; 
  functional induction (ddel B i) => //=;
  move: Heq => /=; rewrite /delete_leaves;
  try (by move => Heq; case: Heq y => <- <- ? <-; case c => //).
  by case => -> ? ->. 
Qed.

Definition dflattenn tr :=
  match tr with
  | Stay t => dflatten t
  | Down t => dflatten t
  end.

Lemma balanceL'E c l r :
  dflattenn (balanceL' mkD c l r) = dflattenn l ++ dflatten r.
Proof. 
  move: l => [] ?; case c; case r => [] [] // [] //= [] [] [] /=; 
  intros; rewrite //= -!catA //= -!catA //. 
Qed.

Lemma balanceR'E c l r :
  dflattenn (balanceR' mkD c l r) = dflatten l ++ dflattenn r.
Proof.
  move: r => [] ?; case c; case l => //= [c'] ? ? [c''|]; 
  try case c'; try case c''; try (intros; rewrite //= -!catA //= -!catA //=);
  move => ? ? [] x; first case x; intros; rewrite //= -!catA //= -!catA //=.
Qed.

Lemma delete_cat {arr arr' : seq bool} {i} :
  delete (arr ++ arr') i = (if i < size arr then delete arr i ++ arr' else arr ++ delete arr' (i - (size arr))).
Proof.
  rewrite /delete take_cat -catA drop_cat.
  case: ifP => H1; case: ifP => // H2; try (move: (ltnW H2); by rewrite H1).
    have H3 : i.+1 = size arr; first by apply/eqP; rewrite eqn_leq H1 leqNgt H2.
    by rewrite H3 subnn drop0 drop_oversize.
  by rewrite catA subSn // leqNgt H1.
Qed.

Lemma delete_leavesE c l r i :
  low <= size l < high -> low <= size r < high ->
  dflattenn (delete_leaves c l r i) = delete (l ++ r) i.
Proof.
  rewrite /delete_leaves delete_cat.
  case: ifP; case: ifP => //; case: ifP => //;
    try rewrite /delete /= take0 drop1 cat0s cat_rcons -!catA.
      case r => //= /eqP -> /eqP <-; by rewrite ltn0.
    case r => //= Hlow0 _ _ _ /andP []; by rewrite leqn0 Hlow0.
  move/eqP => -> /= Hnl Hi /andP [Hl Hl'] Hr'.
  have Hl0 : 0 < size l by move: Hl; rewrite leq_eqVlt Hnl /=; case: (size l).
  rewrite /delete /= /access drop_oversize ?prednK //.
  by rewrite cats0 -cat_rcons -take_nth prednK // take_oversize.
Qed.

Lemma summand_leq a b c: a + b <= c -> a <= c.
Proof.
  elim:b a c => [|b IH] a c;first rewrite addn0 //.
  rewrite addnS => H; move: (ltnW H).
  apply IH.
Qed.
  
Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. case: p => //= p; by rewrite addnS !ltnS leq_subLR. Qed.

Lemma ddelE (B : dtree) i :
  wf_dtree_l B -> dflattenn (ddel B i) = delete (dflatten B) i.
Proof.
  functional induction (ddel B i);
    try (destruct d0 as [nums0 ones0]);
    try rewrite /lt_index /= in e0;
    try (destruct ld as [lnums lones]);
    try (destruct rd as [rnums rones]);
    try move => //= /andP [/eqP Hs] /andP [_] /andP [wfl wfr].
  + by rewrite /= /ddel delete_leavesE.
  + by rewrite /= /ddel delete_leavesE.
  + rewrite balanceL'E delete_leavesE //;
    move: wfl wfr; repeat decompose_rewrite => /=; try by [].
    rewrite !delete_cat //= !size_cat //=.
    repeat case:ifP => //=;
    move:Hs; rewrite size_cat => <-; by rewrite e0.
  + rewrite balanceR'E delete_leavesE //;
    try move: wfl wfr; repeat decompose_rewrite => //=.
    rewrite !delete_cat //= !size_cat //=.
    move:y Hs; case: ifP => //; rewrite size_cat /lt_index /= => y _ Hs.
    move:(Hs)(y)=>->->.
    case: ifP.
      rewrite /leq -subSn;
      last (move:y;rewrite ltnNge Hs; move/negPn; apply summand_leq);
      by rewrite -subnDA subn_eq0 -Hs y.
    by rewrite subnDA !catA.
  + rewrite balanceL'E delete_leavesE //;
    move: wfl wfr; repeat decompose_rewrite => //=.
    rewrite !delete_cat //=.
    repeat case: ifP; try by rewrite !catA.
    move:e0; by rewrite (eqP H1) Hs => ->.
  + rewrite balanceR'E delete_leavesE //;
    try move: wfl wfr; repeat decompose_rewrite => //=.
    rewrite !delete_cat /update_index //=.
    move:y; case: ifP => //; rewrite /lt_index /update_index /= => Hi _.
    rewrite -(eqP H1) -Hs Hi ifF //.
    apply/negP => Hi'; move/negP: Hi; elim.
    rewrite ltn_subLR. by apply /(leq_trans Hi') /leq_addr.
    apply (leq_trans Hlow1); by rewrite (eqP H1).
  + rewrite balanceL'E IHd0; last first.
        move: wfl wfr; repeat decompose_rewrite => /=.
        by rewrite size_cat !dsizeE' // count_cat !donesE' // !eqxx.
      by rewrite !catA [RHS]delete_cat size_cat -Hs ltn_addr.
  + case: ifP y; rewrite // /lt_index /= => e0 _.
    by rewrite balanceR'E delete_cat -Hs e0 IHd0.
  + by rewrite balanceL'E delete_cat -Hs e0 IHd0.
  + rewrite balanceR'E IHd0; last first.
      move: wfl wfr; repeat decompose_rewrite => /=.
      by rewrite dsizeE' // donesE' // !eqxx.
    rewrite -!catA // delete_cat.
    case: ifP => H.
      by case: ifP y => //; rewrite Hs size_cat /lt_index ltn_addr.
    by decomp wfl.
  + by rewrite balanceL'E delete_cat -Hs e0 IHd0.
  + case: ifP y0; rewrite // /lt_index /= => e0 _.
    by rewrite balanceR'E delete_cat -Hs e0 IHd0.
Qed.

Definition identify_deleted_dtree (B : deleted_dtree) : dtree :=
  match B with
  | Stay b => b
  | Down b => b
  end.

Coercion identify_deleted_dtree : deleted_dtree >-> dtree.

Local Notation balanceL' c B b := (balanceL' mkD c B b : deleted_dtree).
Local Notation balanceR' c B b := (balanceR' mkD c B b : deleted_dtree).

Lemma balanceL'_wf (B: deleted_dtree) b c:
  wf_dtree_l B -> wf_dtree_l b -> wf_dtree_l (balanceL' c B b).
Proof.
  case: B b => B b /= wfB wfb.
    by rewrite dsizeE' // donesE' // !eqxx wfB wfb.
  move: c b wfb => [][[][[][[]?[??]?|?][??]?|?][]??[[]?[??]?|?]|?] /=;
   do !decompose_rewrite => //;
   by rewrite !(size_cat,count_cat,addnA,catA,dsizeE',donesE',eqxx,wfB).
Qed.

Lemma balanceR'_wf (B: deleted_dtree) b c:
  wf_dtree_l B -> wf_dtree_l b -> wf_dtree_l (balanceR' c b B).
Proof.
  case: B b => B b /= wfB wfb.
    by rewrite dsizeE' // donesE' // !eqxx wfB wfb.
  move: c b wfb => [][[][[]?[??]?|?][]??[[]?[]??[[]?[??]?|?]|?]|?] /=;
   do! decompose_rewrite => //;
   by rewrite ?(size_cat,count_cat,addnA,catA,dsizeE',donesE',eqxx,wfB).
Qed.

Lemma leq_predr (m n : nat) :
  (m == n) = false -> m <= n -> m <= n.-1.
Proof. rewrite leq_eqVlt => -> /= lo; by rewrite -ltnS (ltn_predK lo). Qed.

Lemma delete_leaves_wf l r i c:
  i < size l + size r ->
  low <= size l < high ->
  low <= size r < high ->
  wf_dtree_l (delete_leaves c l r i).
Proof.
  move=>sc /andP [wll wlh] /andP [wrl wrh].
  have szl: 0 < size l by apply (leq_trans Hlow1).
  have szr: 0 < size r by apply (leq_trans Hlow1).
  have szlp: (size l).-1 < size l by rewrite prednK // subnn.
  have szrp: (size r).-1 < size r by rewrite prednK // subnn.
  rewrite /delete_leaves; do! case: ifP; move=>rc lc /=; try (move=> Hi);
  rewrite ?(size_cat,size_rcons,size_delete,eqxx) //=;
  rewrite ?(prednK,wll,wlh,wrl,wrh) // -?(eqP rc,eqP lc);
  try (by rewrite leq_addr (leq_trans _ Hlow)// -addnn ltn_add2l prednK);
  rewrite ?leq_predr // ?ltn_subLR //; try by rewrite ltnW.
  by rewrite {1}(eqP lc) (eqP rc).
Qed.

Lemma dsize_gt0 (B: dtree) : wf_dtree_l B -> dsize B > 0.
Proof.
  move: B; apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr|s wf] /=.
    by rewrite ltn_addr.
  rewrite (leq_trans Hlow1); by move/andP: wf => [].
Qed.
  
Lemma stay_wfL ll lr r i s:
  s == size (ll ++ lr) -> i < s ->
  low <= size ll < high -> low <= size lr < high -> low <= size r < high ->
  wf_dtree_l (balanceL' Black (delete_leaves Red ll lr i) (Bleaf _ r)).
Proof.
  move=> ic ? wfll wflr wfr.
  by rewrite balanceL'_wf // delete_leaves_wf //= -!size_cat -(eqP ic).
Qed.

Lemma stay_wfR l rl rr i ls:
  ls == size l -> i < size l + size rl + size rr ->
  low <= size l < high -> low <= size rl < high -> low <= size rr < high ->
  wf_dtree_l (balanceR' Black (Bleaf _ l) (delete_leaves Red rl rr (i - ls))).
Proof.
  move=> ic ? wfl wfrl wfrr.
  rewrite balanceR'_wf // delete_leaves_wf //= ltn_subLR ?addnA ?(eqP ic) //.
  apply /(leq_trans (leq_trans Hlow1 _) (leq_addr _ _)). 
  by move/andP: wfrl => [].
Qed.

Lemma ddel_wf (B : dtree) n i :
  n > 0 ->
  is_redblack B Black n ->
  i < dsize B ->
  wf_dtree_l B ->
  wf_dtree_l (ddel B i : deleted_dtree).
Proof.
  move: n; functional induction (ddel B i) => n n_gt0 rbB Hi wf;
    try destruct d0 as [nums0 ones0];
    try destruct rd as [rnums rones];
    try destruct ld as [lnums lones];
    try rewrite /lt_index /= in e0.
  - by rewrite delete_leaves_wf //; decomp wf.
  - by rewrite delete_leaves_wf //; decomp wf.
  - apply /stay_wfL; move: e0; by decomp wf.
  - apply /stay_wfR; by decomp wf.
  - apply (@stay_wfL l0 rl rr i (lnums + rnums)); move: e0;
    try (decomp wf; by rewrite ?size_cat).
    rewrite /update_index /= ltn_subLR //.
    apply (leq_trans Hlow1); by decomp wf.
  - apply /stay_wfR; decomp wf; by rewrite -?addnA.
  - rewrite balanceL'_wf // ?(IHd0 n.-1) //; decomp rbB => //=.
        rewrite (leq_trans e0) //; decomp wf => //=.
        by rewrite size_cat -!dsizeE' // leq_addr.
      decomp wf; by rewrite !(dsizeE',donesE',size_cat,count_cat,eqxx).
    by decomp wf.
  - rewrite balanceR'_wf // ?(IHd0 n.-1) //; decomp rbB => //=; decomp wf => //.
    rewrite ltn_subLR ?size_cat -?dsizeE' //.
    by rewrite (leq_trans (dsize_gt0 H13)) // leq_addr.
  - rewrite balanceL'_wf // ?(IHd0 n.-1) //; decomp rbB => //=; decomp wf => //.
    by rewrite !dsizeE' // -size_cat -(eqP H5).
  - rewrite balanceR'_wf // ?(IHd0 n.-1) //; decomp rbB => //=; decomp wf => //.
      rewrite ltn_subLR ?size_cat -?dsizeE' //; first by rewrite addnA.
      by rewrite (leq_trans (dsize_gt0 H10)) // leq_addr.
    by rewrite !(dsizeE',donesE',eqxx).
  - case: c y rbB Hi wf => //= y; move/andP => [] rbl rbr sc.
      move/andP => [/eqP H] /andP [?] /andP [wfl wfr].
      rewrite balanceL'_wf // (IHd0 n) // ?is_redblack_Red_Black //.
      by rewrite dsizeE' // -H.
    move/andP: rbl => [] _ rbl /andP[/eqP H] /andP[los] /andP[wfl wfr].
    case: n n_gt0 rbl rbr => // n; case neq: n => /= n_gt0.
      move: l0 y sc wfl IHd0 H los => [[] // ll [??] lr|?] //;
      move: r wfr => [[] // rl [??] rr|?] //;
      try move:ll lr =>[[]//|?] [[]//|?] //=;
      try move:rl rr =>[[]//|?] [[]//|?] //=.
      rewrite !size_cat // => wfr _ ? wfl ? H ? _ _.
      rewrite balanceL'_wf // ddel0E delete_leaves_wf //; first (by rewrite -H);
        by decomp wfl.
    move=>rbl rbr; by rewrite balanceL'_wf // (IHd0 n) // ?neq // dsizeE' // -H.
  - case: c y rbB Hi wf => //= y; move/andP => [] rbl rbr sc;
      move/andP => [/eqP H] /andP [los] /andP [wfl wfr].
      rewrite balanceR'_wf // (IHd0 n) // ?is_redblack_Red_Black //.
      by rewrite ltn_subLR // ?H -?dsizeE' // dsize_gt0.
    move/andP: rbl => [] _ rbl.
    case: n n_gt0 rbl rbr => // n; case neq: n => /= n_gt0.
      move: l0 y sc wfl IHd0 H los => /= [[] // ll [??] lr|?] //;
      move: r wfr => [[] // rl [??] rr|?] //;
      try move:ll lr =>[[]//|?] [[]//|?] //=;
      try move:rl rr =>[[]//|?] [[]//|?] //=.
      rewrite !size_cat // => wfr _ ? wfl ? H ? _ _.
      rewrite balanceR'_wf //= ddel0E delete_leaves_wf //; decomp wfr => //.
      by rewrite H ltn_subLR // (leq_trans Hlow1) // (leq_trans H2) // leq_addr.
    move=>rbl rbr; rewrite balanceR'_wf // (IHd0 n) // ?neq // dsizeE' //.
    by rewrite H ltn_subLR // -!dsizeE' // dsize_gt0.
  - by case: n n_gt0 rbB.
Qed.

Lemma ddel_wf' (B : dtree) n i :
  is_redblack B Black n ->
  i < dsize B ->
  wf_dtree' B ->
  wf_dtree' ((ddel B i : deleted_dtree) : dtree).
Proof.
case: n => [|n].
  case: B => [[]// [[]//???|s1] [n1 o1] [[]//???|s2]|s] //=.
    rewrite ddel0E => _ Hi wf.
    apply /wf_dtree_dtree' /delete_leaves_wf => //; by decomp wf.
  move=> _ Hi Hs; rewrite size_delete //.
  by rewrite (ltn_predK Hi) ltnW.
case: B => // c l d r rb Hi wf.
by apply /wf_dtree_dtree' /(@ddel_wf _ n.+1).
Qed.

End ddelete.
