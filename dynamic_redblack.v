From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete set_clear Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section btree.

Variables D A : Type.

Inductive color := Red | Black.

Inductive btree : Type :=
  | Bnode : color -> btree -> D -> btree -> btree
  | Bleaf : A -> btree.

End btree.

Ltac decompose_rewrite :=
  let H := fresh "H" in
  case/andP || (move=>H; rewrite ?H ?(eqP H)).

Section dtree.

Variable w : nat.
Hypothesis Hw : w >= 2.

Definition dtree := btree (nat * nat) (seq bool).

Definition empty_tree : dtree := Bleaf _ [::].

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

Definition rbnode c l r := Bnode c l (dsize l, dones l) r.

Definition bnode l r := Bnode Black l (dsize l, dones l) r.

Definition rnode l r := Bnode Red l (dsize l, dones l) r.

Definition leaf a : dtree := Bleaf _ a.

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

Fixpoint eq_dtree (t1 t2 : dtree) := 
  match t1,t2 with
  | Bleaf a, Bleaf b => a == b
  | Bnode c1 l1 d1 r1, Bnode c2 l2 d2 r2 =>
    (d1 == d2) && (c1 == c2) && (eq_dtree l1 l2) && (eq_dtree r1 r2)
  | Bnode _ _ _ _, Bleaf _ 
  | Bleaf _, Bnode _ _ _ _ => false
  end.

Lemma eq_dtree_refl (t : dtree) : eq_dtree t t.
Proof. elim t => [? l H1 ? r H2 /=|a //=]; by rewrite H1 H2 !eq_refl. Qed.

Lemma eq_dtree_iff t1 t2 : t1 = t2 <-> eq_dtree t1 t2.
Proof.
  split => [->|]; first by rewrite eq_dtree_refl.
  move: t1 t2; elim => [? l1 lH1 ? r1 rH1|?]; elim => [? l2 lH2 ? r2 rH2 H|?] //;
  last by move/eqP => /= ->.
  move/andP: H; case; move/andP; case; move/andP; case; move/eqP => ->; move/eqP => -> H1 H2.
  by rewrite (lH1 _ H1) (rH1 _ H2).
Qed.

Lemma dtree_eqP : Equality.axiom eq_dtree.
Proof.
  move; case => [? l1 ? r1 |?]; case => [? l2 ? r2|?] //;
  set b:= (eq_dtree _ _); case Hb : b; subst b;
  try (apply ReflectT; apply eq_dtree_iff => //); try apply ReflectF => //.
   by case => H1 H2 H3 H4; move: Hb; rewrite H1 H2 H3 H4 eq_dtree_refl.
  by case => H1; move: Hb; rewrite H1 eq_dtree_refl.
Qed.

Canonical dtree_eqMixin := EqMixin dtree_eqP.
Canonical dtree_eqType := Eval hnf in EqType dtree dtree_eqMixin.

Definition access (s : seq bool) i := nth false s i.

Fixpoint wf_dtree (B : dtree) :=
  match B with
  | Bnode _ l (num, ones) r =>
    [&& num == size (dflatten l),
        ones == count_mem true (dflatten l),
        wf_dtree l & wf_dtree r]
  | Bleaf arr =>
    (w ^ 2)./2 <= size arr < (w ^ 2).*2
  end.

Lemma dtree_ind (P : dtree -> Prop) :
  (forall c (l r : dtree) num ones,
      num = size (dflatten l) -> ones = count_mem true (dflatten l) ->
      wf_dtree l /\ wf_dtree r ->
      P l -> P r -> P (Bnode c l (num, ones) r)) ->
  (forall s, (w ^ 2)./2 <= size s < (w ^ 2).*2 -> P (Bleaf _ s)) ->
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

Section insert.

  Definition drank_size B := drank B (dsize B).

  Definition balance col (l : dtree) (r : dtree) : dtree :=
    match col with
    | Red => Bnode Red l (dsize l, drank_size l) r
    | Black => match l, r with
               | Bnode Red (Bnode Red a _ b) _ c, d
               | Bnode Red a _ (Bnode Red b _ c), d
               | a, Bnode Red (Bnode Red b _ c) _ d
               | a, Bnode Red b _ (Bnode Red c _ d)
                 => Bnode Red (Bnode Black a (dsize a, drank_size a) b)
                          (dsize a + dsize b, drank_size a + drank_size b)
                          (Bnode Black c (dsize c, drank_size c) d)
               | _, _ => Bnode Black l (dsize l, drank_size l) r
               end
    end.

  Definition balanceL col (l : dtree) (r : dtree) : dtree :=
    match col with
    | Red => Bnode Red l (dsize l, dones l) r
    | Black => match l with
               | Bnode Red (Bnode Red a _ b) _ c
               | Bnode Red a _ (Bnode Red b _ c)
                   => Bnode Red (Bnode Black a (dsize a, dones a) b)
                          (dsize a + dsize b, dones a + dones b)
                          (Bnode Black c (dsize c, dones c) r)
               | _ => Bnode Black l (dsize l, dones l) r
               end
    end.

  Definition balanceR col (l : dtree) (r : dtree) : dtree :=
    match col with
    | Red => Bnode Red l (dsize l, dones l) r
    | Black => match r with
               | Bnode Red (Bnode Red b _ c) _ d
               | Bnode Red b _ (Bnode Red c _ d)
                   => Bnode Red (Bnode Black l (dsize l, dones l) b)
                          (dsize l + dsize b, dones l + dones b)
                          (Bnode Black c (dsize c, dones c) d)
               | _ => Bnode Black l (dsize l, dones l) r
               end
    end.

  Fixpoint dins (B : dtree) b i : dtree :=
    match B with
    | Bleaf s =>
      let s' := insert1 s b i in
      if size s + 1 == 2 * (w ^ 2)
      then let n  := (size s') %/ 2 in
           let sl := take n s' in
           let sr := drop n s' in
           Bnode Red (Bleaf _ sl) (size sl, count_mem true sl)
                 (Bleaf _ sr)
      else Bleaf _ s'
    | Bnode c l (num, ones) r =>
      if i < num
      then balanceL c (dins l b i) r
      else balanceR c l (dins r b (i - num))
    end.

  Definition dinsert (B : dtree) b i : dtree :=
    match dins B b i with
    | Bleaf s => Bleaf _ s
    | Bnode _ l d r => Bnode Black l d r
    end.

  (* Correctness lemmas *)

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

  Lemma dinsE (B : dtree) b i :
    wf_dtree B -> dflatten (dins B b i) = insert1 (dflatten B) b i.
  Proof.
    move => wf; move: B wf b i. apply: dtree_ind => //.
    + move => c l r num ones Hnum Hones _ IHl IHr /= b i.
      case: ifPn => ?.
      - by rewrite balanceLE IHl /insert1 insert_catL -?Hnum.
      - by rewrite balanceRE IHr /insert1 insert_catR -?Hnum // leqNgt.
    + move => s Hs b i.
      rewrite /dins. case: ifP => Hi //.
      by rewrite dflatten_node /dflatten cat_take_drop.
  Qed.

  Lemma dinsertE (B : dtree) b i :
    wf_dtree B -> dflatten (dinsert B b i) = insert1 (dflatten B) b i.
  Proof. move => wf. rewrite /dinsert -(dinsE b i wf). by case: dins. Qed.

  (* Well-foundedness lemmas
   * Show that dinsert always returns a well-founded tree
   *)

  Lemma balanceL_wf c (l r : dtree) :
    wf_dtree l -> wf_dtree r -> wf_dtree (balanceL c l r).
  Proof.
    case: c => /= wfl wfr.
      by rewrite wfl wfr ?(dsizeE,donesE,eqxx).
    case: l wfl =>
      [[[[] lll [lln llo] llr|llA] [ln lo] [[] lrl [lrn lro] lrr|lrA]
       |ll [ln lo] lr]|lA] /=;
      rewrite wfr; repeat decompose_rewrite;
      by rewrite ?(dsizeE,donesE,size_cat,count_cat,eqxx).
  Qed.

  Lemma balanceR_wf c (l r : dtree) :
    wf_dtree l -> wf_dtree r -> wf_dtree (balanceR c l r).
  Proof.
    case: c => /= wfl wfr.
      by rewrite wfl wfr ?(dsizeE,donesE,eqxx).
    case: r wfr => [[[[] rll [rln rlo] rlr|rlA] [rn ro] [[] rrl
                             [rrn rro] rrr|rrA]|rl [rn ro] rr]|rA] /=;
      rewrite wfl; repeat decompose_rewrite;
      by rewrite ?(dsizeE,donesE,size_cat,count_cat,eqxx).
  Qed.

  Lemma leq_half n : n./2 <= n.
  Proof. by rewrite -{2}(odd_double_half n) -addnn addnA leq_addl. Qed.

  Lemma dins_wf (B : dtree) b i :
    wf_dtree B -> wf_dtree (dins B b i).
  Proof.
    move => wf;  move: B wf b i.
    apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr b i | s Hs b i] /=.
    case: ifP => Hi. by apply: balanceL_wf.
    by apply: balanceR_wf.
    rewrite addn1 divn2 mul2n.
    case: ifP => Hsize /=.
    rewrite ?(eqxx,size_insert1,(eqP Hsize),size_drop,size_takel).
    rewrite doubleK -[X in X - _]addnn addnK leq_half -muln2 ltn_Pmulr //.
    by rewrite sqrn_gt0 (leq_trans _ Hw).
    by rewrite leq_half.
    rewrite size_insert1.
    move/andP: Hs => [Hs1].
    rewrite leq_eqVlt Hsize /= => ->.
    by rewrite (leq_trans Hs1).
  Qed.

  Lemma recolor_node_wf c c' d (l r : dtree) :
    wf_dtree (Bnode c l d r) -> wf_dtree (Bnode c' l d r).
  Proof. by []. Qed.

  Lemma dinsert_wf (B : dtree) b i :
    wf_dtree B -> wf_dtree (dinsert B b i).
  Proof.
    move => wf. rewrite /dinsert.
    case Hins: (dins B b i) => [c l [num ones] r | s] //.
      apply: (@recolor_node_wf c).
      by rewrite -Hins dins_wf.
    by rewrite -Hins dins_wf.
  Qed.

  Lemma dinsert_rank (B : dtree) b i j :
    wf_dtree B -> drank (dinsert B b i) j =
                  rank true j (insert1 (dflatten B) b i).
  Proof. move => wf. by rewrite -dinsertE // drankE // dinsert_wf. Qed.

  Lemma dinsert_select1 (B : dtree) b i j : wf_dtree B ->
    dselect_1 (dinsert B b i) j = select true j (insert1 (dflatten B) b i).
  Proof.
    move => wf. by rewrite -dinsertE // dselect_1E // dinsert_wf.
  Qed.

  Lemma dinsert_select0 (B : dtree) b i j : wf_dtree B ->
    dselect_0 (dinsert B b i) j = select false j (insert1 (dflatten B) b i).
  Proof.
    move => wf. by rewrite -dinsertE // dselect_0E // dinsert_wf.
  Qed.

  (*
   * Following Appel (2011), pp. 6 - 8
   *
   * ctxt = "color context", or the color of
   * the parent node
   *
   * bh = "black height", i.e. # of black nodes on the
   * path from the root
   *)
  Fixpoint is_redblack (B : dtree) ctxt bh :=
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

  Definition nearly_redblack (B : dtree) bh :=
    match B with
    | Bnode Red l _ r => is_redblack l Black bh && is_redblack r Black bh
    | _ => is_redblack B Black bh
    end.

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
    case: B => /= -[]; case: c => // l p r /andP [Hl Hr].
    by rewrite !is_redblack_Red_Black.
  Qed.

  Lemma dins_is_redblack (B : dtree) b i n :
    (is_redblack B Black n -> nearly_redblack (dins B b i) n) /\
    (is_redblack B Red n -> is_redblack (dins B b i) Black n).
  Proof.
    elim: B i n => [c l IHl [num ones] r IHr | a] i n;
      last by split => /=; case: ifP => //= _ ->.
    have Hbk : is_redblack (Bnode Black l (num, ones) r) Black n ->
               is_redblack (dins (Bnode Black l (num, ones) r) b i) Black n.
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

  Lemma dinsert_is_redblack (B : dtree) b i n :
    is_redblack B Red n -> exists n', is_redblack (dinsert B b i) Red n'.
  Proof.
    exists (if (dins B b i) is Bnode Red _ _ _ then n + 1 else n).
    move/(proj2 (dins_is_redblack _ b i _)): H.
    rewrite /dinsert addnC.
    destruct dins => //=.
    case: c => //= /andP [Hd1 Hd2].
    by rewrite !is_redblack_Red_Black.
  Qed.

  Definition is_red D A (B : btree D A) :=
    if B is Bnode Red _ _ _ then true else false.

  Lemma dinsert_is_nearly_redblack' (B : dtree) b i n :
    is_redblack B Red n ->
    is_redblack (dinsert B b i) Red (n + is_red (dins B b i)).
  Proof.
    move/(proj2 (dins_is_redblack _ b i _)).
    rewrite /dinsert addnC.
    destruct dins => //=.
    case: c => //= /andP [Hd1 Hd2].
    by rewrite !is_redblack_Red_Black.
  Qed.

End insert.

Section set_clear.

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
    wf_dtree B -> dflatten (dbitset B i) = bit_set (dflatten B) i.
  Proof.
    move=> wf; move: B wf i; rewrite /bit_set.
    apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i /=.
    rewrite update_cat -IHl -IHr /dbitset /=.
    by case: ifP => Hi; case: bset => // l' [].
  Qed.

  Lemma dbitclearE (B : dtree) i :
    wf_dtree B -> dflatten (dbitclear B i) = bit_clear (dflatten B) i.
  Proof.
    move=> wf; move: B wf i; rewrite /bit_clear.
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
    wf_dtree B -> i < dsize B -> (bset B i).2 = ~~ (daccess B i).
  Proof.
    move=> wf; move: B wf i.
    apply: dtree_ind; last first.
      move=> s Hs i Hi; congr negb; by apply set_nth_default.
    move=> c l r num ones Hnum Hones [wfl wfr] IHl IHr i /= IHsize.
    rewrite Hnum -dsizeE //.
    case: ifP => Hi.
      by rewrite -IHl; case: bset.
    rewrite -IHr; case: bset => // _ _.
    by rewrite -subSn ?leq_subLR // leqNgt Hi.
  Qed.

  Lemma flip_bit_bclear (B : dtree) i :
    wf_dtree B -> i < dsize B -> (bclear B i).2 = daccess B i.
  Proof.
    move=> wf; move: B wf i.
    apply: dtree_ind; last first.
      move => s Hs i Hi; by apply set_nth_default.
    move => c l r num ones Hnum Hones [wfl wfr] IHl IHr i /= IHsize.
    rewrite Hnum -dsizeE //.
    case: ifP => Hi.
      by rewrite -IHl; case: bclear.
    rewrite -IHr; case: bclear => // _ _.
    by rewrite -subSn ?leq_subLR // leqNgt Hi.
  Qed.

  Lemma dones_dbitset (B : dtree) i :
    wf_dtree B -> i < dsize B ->
    dones (dbitset B i) = dones B + ~~ daccess B i.
  Proof.
    rewrite /dbitset.
    move=> wf Hsize; move: B wf i Hsize.
    apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi | s Hs i Hi].
    rewrite -dsizeE //.
    case: ifP => Hil.
    case_eq (bset l i) => l' b Hbset /=.
    by rewrite addnAC -IHl // Hbset.
    case_eq (bset r (i - dsize l)) => r' b Hbset /=.
    rewrite -addnA -IHr ?Hbset //.
    by rewrite -(ltn_add2l (dsize l)) subnKC // leqNgt Hil.
    by rewrite addnC -count_bit_set.
  Qed.

  Lemma flipped_count_pos (B : dtree) i :
    wf_dtree B -> i < dsize B -> (bclear B i).2 -> dones B > 0.
  Proof.
    move=> wf Hsize; rewrite flip_bit_bclear // daccessE // /access => H.
    by rewrite donesE // (true_count_pos _ H) // -dsizeE.
  Qed.

  Lemma dones_dbitclear (B : dtree) i :
    wf_dtree B -> i < dsize B ->
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
    wf_dtree B -> wf_dtree (dbitset B i).
  Proof.
    move => wf; move: B wf i.
    apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr|s Hs] i;
      last by rewrite size_bit_set.
    rewrite /dbitset //=.
    case: ifP => Hi.
      case_eq (bset l i) => l' b Hbset /=; rewrite wfr andbT.
      move/(f_equal fst): (Hbset) => /= Hbset1.
      move/(_ i) in IHl; rewrite /dbitset Hbset1 in IHl.
      rewrite -!dsizeE // -Hbset1 dsize_bset -!donesE ?[in wf_dtree _]Hbset1 //.
      by rewrite dones_dbitset // -?flip_bit_bset // ?dsizeE // Hbset !eqxx.
    case_eq (bset r (i - (size (dflatten l)))) => r' b /(f_equal fst) /= <-.
    by rewrite wfl !eqxx /= IHr.
  Qed.

  Lemma wf_dbitclear (B : dtree) i :
    wf_dtree B -> wf_dtree (dbitclear B i).
  Proof.
    move => wf; move: B wf i.
    apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr|s Hs] i /=;
      last by rewrite size_bit_clear.
    rewrite /dbitclear //=.
    case: ifP => Hi.
      case_eq (bclear l i) => l' b Hbclear /=; rewrite wfr andbT.
      move/(f_equal fst): (Hbclear) => /= Hbclear1.
      move/(_ i) in IHl; rewrite /dbitclear Hbclear1 in IHl.
      by rewrite -!dsizeE // -Hbclear1 dsize_bclear -!donesE //
                [in wf_dtree _]Hbclear1 // dones_dbitclear //
                -?flip_bit_bclear // ?dsizeE // Hbclear !eqxx.
    case_eq (bclear r (i - (size (dflatten l)))) => r' b /(f_equal fst) /= <-.
    by rewrite wfl !eqxx /= IHr.
  Qed.

End set_clear.

Section delete.

  Inductive deleted_dtree: Type :=
  | Stay : dtree -> deleted_dtree
  | Down : dtree -> deleted_dtree.

  Definition balanceL' col (l : deleted_dtree) (r : dtree) : deleted_dtree :=
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
  
  Definition balanceR' col (l : dtree) (r : deleted_dtree) : deleted_dtree :=
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

  Definition delete_leaves p l r (i : nat) : deleted_dtree :=
    if i < size l
    then match (w ^ 2)./2 == size l,(w ^ 2)./2 == size r with
         | true,true =>
           Down (leaf ((rcons (delete l i) (access r 0)) ++ (delete r 0)))
         | true,false => 
           Stay (rbnode p (leaf (rcons (delete l i) (access r 0))) (leaf (delete r 0)))
         | false,_ => 
           Stay (rbnode p (leaf (delete l i)) (leaf r))
         end
    else match (w ^ 2)./2 == size l,(w ^ 2)./2 == size r with
         | true,true =>
           Down (leaf (l ++ (delete r (i - (size l)))))
         | false,true => 
           Stay (rbnode p (leaf (delete l (size l).-1)) (leaf ((access l (size l).-1) :: (delete r (i - size l)))))
         | _,false => 
           Stay (rbnode p (leaf l) (leaf (delete r (i - (size l)))))
         end.

  Fixpoint height_of_dtree (B : dtree) :=
    match B with
    | Bnode Black l _ r => (maxn (height_of_dtree l) (height_of_dtree r)).+2
    | Bnode Red l _ r => (maxn (height_of_dtree l) (height_of_dtree r)).+1
    | Bleaf _ => 0
    end.

  Lemma hc_pcl {l r c s n} :
    height_of_dtree l < height_of_dtree (Bnode c l (s, n) r).
  Proof.
    case c; rewrite /= -!maxnSS leq_max ltnS;
    [ rewrite leqnn // | rewrite ltnW // ].
  Qed.

  Lemma hc_pcr {l r c s n} :
    height_of_dtree r < height_of_dtree (Bnode c l (s, n) r).
  Proof.
    case c; rewrite /= -!maxnSS leq_max ltnS;
    [ rewrite leqnn orbT // | apply/orP; right; rewrite ltnW // ]. 
  Qed.

  Lemma hc_pcl' {lr ll r s p n} :
    height_of_dtree (rnode lr r) < height_of_dtree (Bnode Black (Bnode Red ll p lr) (s, n) r).
  Proof.
    rewrite /= -!maxnSS -maxnA !leq_max !/maxn; case: ifP => H;
    [ rewrite ltnSn !orbT // | rewrite [ _.+1 < (_ lr).+3]ltnW // orbT // ]. 
  Qed.

  Lemma hc_pcr' {l rl rr s n p} :
    height_of_dtree (rnode l rl) < height_of_dtree (Bnode Black l (s, n) (Bnode Red rl p rr)).
  Proof.
    rewrite /= -!maxnSS maxnA !leq_max !/maxn; case: ifP => H;
   [ rewrite [ _.+1 < (_ rl).+3]ltnW // orbT // | rewrite ltnSn // ]. 
  Qed.
  
  Lemma hc_pcr'' {ll lr rl rr lc l' dr}:
    height_of_dtree (rnode (rbnode lc ll lr) (bnode rl rr)) <
    height_of_dtree (bnode (rnode (leaf l') (rbnode lc ll lr)) (Bnode Black rl dr rr)).
  Proof.
    move: lc => /= []; rewrite max0n !maxnSS /= /leq !subSS subn_eq0;
    rewrite /= -!maxnSS maxnA !leq_max !/maxn;
    repeat case: ifP;
    try rewrite leqnn //=;
    try rewrite leqnSn //=;
    by (intros; rewrite !orbT).
  Qed.

  Function ddel (B : dtree) (i : nat) { measure height_of_dtree B } : deleted_dtree :=
    match B with
    | Bnode Black (Bleaf l) (s,o) (Bleaf r) => delete_leaves Black l r i
    | Bnode Red (Bleaf l) (s,o) (Bleaf r) => delete_leaves Red l r i
                                                           
    | Bnode Black (Bnode Red (Bleaf ll) (ls,_) (Bleaf lr)) (s,_) (Bleaf r) => 
      if i < s
      then balanceL' Black (delete_leaves Red ll lr i) (Bleaf _ r)
      else balanceR' Black (Bleaf _ ll) (delete_leaves Red lr r (i - ls))
                                                           
    | Bnode Black (Bleaf l) (ls,_) (Bnode Red (Bleaf rl) (rs,_) (Bleaf rr)) => 
      if i < ls + rs
      then balanceL' Black (delete_leaves Red l rl i) (Bleaf _ rr)
      else balanceR' Black (Bleaf _ l) (delete_leaves Red rl rr (i - ls))
                     
    | Bnode Black (Bnode Black ll (ls,lo) lr) (s,_) (Bnode Red rl (rs,ro) rr) =>
      let l := Bnode Black ll (ls,lo) lr in
      let r := Bnode Red rl (rs,ro) rr in
      if i < s
      then balanceL' Black (ddel (rnode l rl) i) rr
      else balanceR' Black l (ddel r (i - s))
    | Bnode Black (Bnode Red ll (ls,lo) lr) (s,_) (Bnode Black rl (rs,ro) rr) =>
      let l := Bnode Red ll (ls,lo) lr in
      let r := Bnode Black rl (rs,ro) rr in
      if i < s
      then balanceL' Black (ddel l i) r
      else balanceR' Black ll (ddel (rnode lr r) (i - ls))
    | Bnode c l (s,_) r => 
      if i < s
      then balanceL' c (ddel l i) r
      else balanceR' c l (ddel r (i - s))
    (* absurd case *)
    | Bleaf x =>  Stay (leaf (delete x i))
    end.

  all: intros; subst B; apply/leP; 
  try (apply/eqP; rewrite /= subSS; apply/eqP; try (by apply leq_maxl); by apply leq_maxr); 
  try (apply hc_pcl); try (apply hc_pcr).
  apply hc_pcl'.
  apply hc_pcr''.
  apply hc_pcr'.
  Defined.

  Lemma ddel0E s o l r i :
    ddel (Bnode Red (Bleaf (nat * nat) l) (s,o) (Bleaf (nat * nat) r)) i = delete_leaves Red l r i.
  Proof.
    move Heq : (Bnode Red _ _ _) => B; 
    functional induction (ddel B i) => //=; 
    move: Heq => /=; try (by move => Heq; case: Heq y => <- <- ? ? <-; case c => //);
    by case => -> ? ? ->. 
  Qed.

  Definition dflattenn tr :=
    match tr with
    | Stay t => dflatten t
    | Down t => dflatten t
    end.

  Lemma balanceL'E c l r : dflattenn (balanceL' c l r) = dflattenn l ++ dflatten r.
  Proof. 
    move: l => [] ?; case c; case r => [] [] // [] //= [] [] [] /=; 
    intros; rewrite //= -!catA //= -!catA //. 
  Qed.

  Lemma balanceR'E c l r : dflattenn (balanceR' c l r) = dflatten l ++ dflattenn r.
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
    (w ^ 2)./2 <= size l < (w ^ 2).*2 -> (w ^ 2)./2 <= size r < (w ^ 2).*2 ->
    dflattenn (delete_leaves c l r i) = delete (l ++ r) i.
  Proof.
    rewrite /delete_leaves delete_cat.
    case: ifP; case: ifP => //; case: ifP => //;
    try (rewrite /delete /= take0 drop1 cat0s cat_rcons -!catA;
         case r => //; move: Hw; by case w => // -[]).
    move => Hr Hnl Hi /andP [Hl Hl'] Hr'.
    have Hp : (w ^ 2)./2 > 0 by move: Hw; case w => // -[].
    have l_gt0 := leq_trans Hp Hl.
    rewrite /delete /= /access drop_oversize ?prednK //.
    by rewrite cats0 -cat_rcons -take_nth prednK // take_oversize.
  Qed.

  Lemma summand_leq a b c: a + b <= c -> a <= c.
  Proof.
    elim:b a c => [|b IH] a c;first rewrite addn0 //.
    rewrite addnS => H; move: (ltnW H).
    apply IH.
  Qed.
  
  Lemma positivity_w x : x >= (w ^ 2)./2 -> 0 < x.
  Proof. case: x Hw => //; case => // x. case: w Hw => //; case => //. Qed.
  
  Lemma ddelE (B : dtree) i :
    wf_dtree B -> dflattenn (ddel B i) = delete (dflatten B) i.
  Proof.
    functional induction (ddel B i)
      => //= /andP [/eqP Hs] /andP [_] /andP [wfl wfr].
    + by rewrite /= /ddel delete_leavesE.
    + by rewrite /= /ddel delete_leavesE.
    + rewrite balanceL'E delete_leavesE //;
      move: wfl wfr; repeat decompose_rewrite => /=; try by [].
      rewrite !delete_cat //= !size_cat //=.
      repeat case:ifP => //=;
      move:Hs; rewrite size_cat => <-; rewrite e0 //.
      
    + rewrite balanceR'E delete_leavesE //;
      try move: wfl wfr; repeat decompose_rewrite => //=.
      rewrite !delete_cat //= !size_cat //=.
      move:y Hs; case: ifP => //; rewrite size_cat=>y _ Hs.
      move:(Hs)(y)=>->->.
      case: ifP.
       rewrite /leq -subSn;
       last (move:y;rewrite ltnNge Hs; move/negPn; apply summand_leq);
       rewrite -subnDA subn_eq0 -Hs y //.
      rewrite subnDA !catA //=.
      
    + rewrite balanceL'E delete_leavesE //;
      move: wfl wfr; repeat decompose_rewrite => /=; try by [].
      rewrite !delete_cat //=.
      repeat case: ifP; try by rewrite !catA.
      move:e0;move/eqP:H1=>->;move:Hs=>-> X Y Z.
      move:Z; rewrite ltnNge /=; move/negPn=>?.
      move:X Y; rewrite /leq.
      rewrite -subSn // !subnDA => -> //.
      
    + rewrite balanceR'E delete_leavesE //;
      try move: wfl wfr; repeat decompose_rewrite => //=.
      rewrite !delete_cat //=.
      move:y;case: ifP => //;rewrite ltnNge;move/negPn=>y _.
      move/eqP:(H1) (Hs) y =>->-> y.
      repeat case: ifP;
      try by rewrite !catA;
      try by rewrite ltnNge (summand_leq y).
      
    + rewrite balanceL'E IHd; last first.
        move: wfl wfr; repeat decompose_rewrite => /=.
        by rewrite size_cat !dsizeE // count_cat !donesE // !eq_refl.
      by rewrite !catA [RHS]delete_cat size_cat -Hs ltn_addr.
      
    + case: ifP y => // e0 _.
      by rewrite balanceR'E delete_cat -Hs e0 IHd.
    + by rewrite balanceL'E delete_cat -Hs e0 IHd.
    + rewrite balanceR'E IHd; last first.
        move: wfl wfr; repeat decompose_rewrite => /=.
        by rewrite dsizeE // donesE // !eq_refl.
      rewrite -!catA // delete_cat.
      case: ifP => H.
        by case: ifP y => //; rewrite Hs size_cat ltn_addr.
      by move: wfl; repeat decompose_rewrite => //.
    + by rewrite balanceL'E delete_cat -Hs e0 IHd.
    + case: ifP y0 => // e0 _.
      by rewrite balanceR'E delete_cat -Hs e0 IHd.
  Qed.

  Definition is_nearly_redblack' tr c bh :=
    match tr with
    | Stay tr => is_redblack tr c bh
    | Down tr => is_redblack tr Red bh.-1
    end.
  
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
    repeat decompose_rewrite => //; by rewrite !is_redblack_Red_Black.
  Qed.
  
  Lemma balanceL'_Red_nearly_is_redblack l r n :
    is_nearly_redblack' l Red n -> is_redblack r Red n ->
    is_nearly_redblack' (balanceL' Red l r) Black n.
  Proof.
    case: l => [l /= -> -> // | l okl okr].
    case: r l okr okl => [ [//|] [[] rll ? rlr| ?] ? rr | ?] l /=;
    repeat decompose_rewrite => //; by rewrite !is_redblack_Red_Black.
  Qed.
    
  Lemma balanceR'_Black_nearly_is_redblack l r n c :
    0 < n -> is_redblack l Black n.-1 -> is_nearly_redblack' r Black n.-1 ->
    is_nearly_redblack' (balanceR' Black l r) c n.
  Proof.
    case: r => [r /= -> -> -> //| //].
    case: c n l => [] [//|n] [[[[] lll ? llr|?] ?
      [[] lrl ? [[] lrrl ? lrrr|?]|?]|ll ? [[] lrl ? lrr|?]]|?] /=;
    repeat decompose_rewrite => //; by rewrite !is_redblack_Red_Black. 
  Qed.
  
  Lemma balanceR'_Red_nearly_is_redblack l r n :
    is_redblack l Red n -> is_nearly_redblack' r Red n ->
    is_nearly_redblack' (balanceR' Red l r) Black n.
  Proof.
    case: r => [r /= -> -> //| //].
    case: l => [ [//|] ll ? [[] lrl ? lrr|?] |?] r /=;
    repeat decompose_rewrite => //; by rewrite !is_redblack_Red_Black. 
  Qed.
  
Ltac decomp ok := move: ok => /=; repeat decompose_rewrite.
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
  0 < n -> is_redblack B c n -> is_nearly_redblack' (ddel B i) c n.
Proof.
move: n c; functional induction (ddel B i) => n c' H.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ rewrite /delete_leaves.
  case: c' => /= ok; by decomp_ifP ok.
+ move=> ok; solveL' IHd ok => //.
  by apply is_redblack_Red_Black.
+ move=> ok; by solveR' IHd ok.
+ move=> ok; by solveL' IHd ok.
+ move=> ok; solveR' IHd ok => //.
  by apply is_redblack_Red_Black.
+ move: c c' l r y IHd =>
    [] [] // [[] ll [] ? ? lr |?] [[] // rl [] ? ? rr|?] //= y IHd;
  first (by rewrite !andbF);
  try (case/andP => C /eqP H'; case/andP: C; by rewrite H' ltnn /=);
  move => ok;
  first (by rewrite balanceL'_Red_nearly_is_redblack // ?IHd //; decomp ok);
  splitL' ll y IHd ok;
  splitL' lr y IHd ok;
  try splitL' rl y IHd ok;
  by rewrite ddel0E /delete_leaves; decomp_ifP ok.
+ move: c c' l r y IHd =>
    [] [] // [[] ll [] ? ? lr |?] [[] // rl [] ? ? rr|?] //= y IHd;
  try (by rewrite !andbF);
  try (case/andP => /eqP ->; by rewrite ltnn /=);
  move => ok;
  first (by rewrite balanceR'_Red_nearly_is_redblack // ?IHd //; decomp ok);
  splitR' rl y IHd ok;
  splitR' rr y IHd ok;
  try splitR' lr y IHd ok;
  by rewrite ddel0E /delete_leaves; decomp_ifP ok.
+ by [].
Qed.

Definition identify_deleted_dtree B :=
  match B with
  | Stay b => b
  | Down b => b
  end.

Lemma size_pf_leq1 : (w ^ 2)./2 <= ((w ^ 2)./2.-1).*2.+1.
Proof.
  have Lem : forall x, x > 1 -> x <= (x.-1).*2.+1.
   move=> x H.
   have: (x.-1).*2.+1 == x.*2.-1. elim: x H => //.
   move/eqP=> ->.
   case: x H => // w' H.
   by rewrite -addnn -subn1 -addn1 addnA addnK leq_addr.
  apply Lem.
  case: w Hw => //; case => // w' ?.
  by rewrite -[in _./2]add2n sqrnD -divn2 leq_divRL //.
Qed.

Lemma trivial_lem x : 0 < x -> 1 < x.*2.
Proof. case: x => //. Qed.
  
Lemma size_pf_ltn1 : ((w ^ 2)./2.-1).*2.+1 < (w ^ 2).*2.
Proof.
  rewrite -divn2.
  have l1: 1 < (w ^ 2). case: w Hw => //; case => //.
  have Lem1: 0 < w ^ 2 %/ 2.
   case: w Hw => //; case => // ? ?.
   rewrite -addn2 sqrnD divnDr; last repeat apply dvdn_mull => //.
   apply ltn_addr => //.
   rewrite leq_divRL //.
   apply ltn_addl => //.
  have Lem2: 1 < (w ^ 2 %/ 2).*2. by apply trivial_lem.
  have l2: ((w ^ 2 %/ 2).-1).*2 < (w ^ 2).
   have l2': (w ^ 2 %/ 2).*2 <= w ^ 2. rewrite -muln2; apply leq_trunc_div => //.
    apply ltnW.
    rewrite -addnn -subn1 addnBA // addnC addnBA // !subn1 addnn -subn2 -addn2 subnK //.
  apply ltnW.
  move: (@leq_add _ _ _ _ l1 l2).
  by rewrite add2n addnn.
Qed.

Lemma double_pos x : 0 < x -> x < x.*2.
Proof.
  move=> H.
  rewrite -addnn.
  case: x H => // x H.
  by rewrite -2!addn1 addnAC -!addnA leq_addl.
Qed.

Lemma trivial_lem2 x : 0 < x -> x %/ 2 < x.
Proof.
  rewrite ltn_divLR // => H.
  rewrite muln2 double_pos //.
Qed.

Lemma size_pf_ltn2 : w ^ 2 %/ 2 < (w ^ 2).*2.
Proof.
  elim: w Hw => //; case => //= w' IH H.
  rewrite -addnn.
  apply ltn_addr.
  apply trivial_lem2.
  rewrite -addn2 sqrnD ltn_addr // ltn_addl //.
Qed.

Coercion identify_deleted_dtree : deleted_dtree >-> dtree.

Lemma balanceL'_wf (B: deleted_dtree) b c:
  wf_dtree B -> wf_dtree b -> wf_dtree (balanceL' c B b).
Proof.
  case: B b => B b /= wfB wfb.
    by rewrite dsizeE // donesE // !eqxx wfB wfb.
  move:c b wfb=>[][[][[][[]?[]???|?][]???|?][]??[[]?[]???|?]|?] wfb /=;
   try decomp wfb => //;
   by rewrite !(size_cat,count_cat,addnA,catA,dsizeE,donesE,eqxx,wfB).
Qed.

Lemma leq_predr (m n : nat) :
  (m == n) = false -> m <= n -> m <= n.-1.
Proof. rewrite leq_eqVlt => -> /= lo; by rewrite -ltnS (ltn_predK lo). Qed.

Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Proof. case: p => //= p; by rewrite addnS !ltnS leq_subLR. Qed.

Lemma wordsize_sqrn_2_gt1 : (w ^ 2)./2 > 1.
Proof.
  rewrite /leq.
  have zt:0 = 0.*2 by rewrite -mul2n muln0.
  apply/eqP; rewrite [in RHS]zt; apply/eqP.
  rewrite -!muln2 eqn_mul //; last first.
   case:w Hw=>//-[]// w' _.
   rewrite -[w'.+2]addn2 sqrnD -!divn2.
   rewrite divnDr //; last rewrite dvdn_mull //; last rewrite dvdn_mull //.
   rewrite divnDr //.
   rewrite !divn2 /= addnC !addnA addnC !subnDA; by compute.
  apply/eqP; rewrite divn_small //.
  rewrite /leq subnS -addn1 addnK -subnS subSS subn_eq0.
  case:w Hw=>//-[]//.
Qed.

Lemma dellvs_wf l r i c:
  i < size l + size r ->
  (w ^ 2)./2 <= size l < (w ^ 2).*2 ->
  (w ^ 2)./2 <= size r < (w ^ 2).*2 ->
  wf_dtree (delete_leaves c l r i).
Proof.
  move=>sc wl wr.
  have?:(w ^ 2) > 0 by move: Hw; case w => // -[].
  have?:(w ^ 2)./2 > 0 by move: Hw; case w => // -[].
  have?:0 < size r by apply positivity_w; move/andP:wr=>[]//.
  have?:0 < size l by apply positivity_w; move/andP:wl=>[]//.
  have?:(size l).-1 < size l by rewrite /leq (@ltn_predK 0 _) // subnn //.
  rewrite /delete_leaves;
  repeat case: ifP; move=>rc lc /=;
  try move=>?;
  try rewrite !eq_refl /=;
  try rewrite add0n subn1;
  try rewrite !size_delete //;
  try rewrite size_cat // !size_delete //;
  try rewrite !size_rcons !size_delete //;
  try rewrite leq_predr //;
  try rewrite ltn_subLR // addnC //;
  try rewrite [_.-1 < _]ltnW //;
  try rewrite (@ltn_predK 0 _) //;
  try (move/eqP:lc=><-; move/eqP:rc=><-);
  try by decomp wl;
  try by decomp wr;
  try by (apply/andP;split; first rewrite leq_addr //;
   rewrite /leq -addnS (@ltn_predK 0 _) // addnn subn_eq0 -!muln2 leq_mul2r /= -divn2 ltnW // trivial_lem2 //).
Qed.

Lemma positivity (B: dtree) : wf_dtree B -> dsize B > 0.
Proof.
  elim:B=>/= [? l IHl []?? r IHr|?] wf;
  first rewrite ltn_addr // IHl //; 
  last apply positivity_w; by decomp wf.
Qed.
  
Lemma balanceR'_wf (B: deleted_dtree) b c:
  wf_dtree B ->
  wf_dtree b ->
  wf_dtree (balanceR' c b B).
Proof.
  case: B b => B b /= wfB wfb.
   by rewrite dsizeE // donesE // !eq_refl wfB wfb.
   
  move:c b wfb=>[][[][[]?[]???|?][]??[[]?[]??[[]?[]???|?]|?]|?] wfb /=;
   try decomp wfb => //;
   try rewrite !size_cat !count_cat;
   try rewrite !addnA;
   try rewrite !catA;
   try rewrite !size_cat !count_cat;
   try rewrite !dsizeE //;
   try rewrite !donesE //;
   by rewrite !eq_refl wfB //.
Qed.

Lemma ddel_wf (B : dtree) n i :
  n > 0 ->
  is_redblack B Black n ->
  i < dsize B ->
  wf_dtree B ->
  wf_dtree (ddel B i).
Proof.
  have Hp : (w ^ 2)./2 > 0 by move: Hw; case w => // -[].
  move: n; functional induction (ddel B i) => //= n n_gt0.
  -move => rbBn sc wfB.
   rewrite /delete_leaves.
   repeat case: ifP => //.
   *move/eqP => wr; move/eqP => wl.
    move => ? /=; rewrite size_cat size_rcons !size_delete // -wr // -wl addSn addnn; apply/andP; split; first apply size_pf_leq1; apply size_pf_ltn1.
   
   *move=> wr; move/eqP => wl.
    move => ? /=; rewrite size_cat size_rcons !size_delete // -addn1 -subn1 subnK; last rewrite -wl //.
    repeat (apply/andP; split => //); try rewrite -wl; try by [].
     +rewrite -divn2 size_pf_ltn2 //.
     +move/andP: wfB => [] ?; move/andP => [] ?; move/andP => [] ?; move/andP=> [] H ?; move: (H).
      rewrite leq_eqVlt wr /= size_drop /leq; move/eqP => H'.
      rewrite -subSKn subnDA -subnS -[in (size _ - _).+1]addn1 -subnDA addnC subnK; last apply positivity_w => //.
      by rewrite subnDA H' sub0n.
     +rewrite size_drop size_take.
      move/andP: wfB => [] ?; move/andP => [] ?; move/andP => [] ?; move/andP=> [] H; move: (positivity_w H) => H' ?.
      rewrite H' add0n -addn1 subnK //; by apply ltnW.
      
   *move=> wl ?.
    rewrite /= !eq_refl /= size_delete //.
    repeat (apply/andP => []; split); try by (move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ?).
     +move/andP: wfB => [] ?; move/andP => [] ?; move/andP => [];move/andP => [] H'; move: (H').
      rewrite leq_eqVlt wl /leq /= => ? ? ?.
      rewrite -subn1 subnBA; last apply positivity_w => //.
      by rewrite addn1.
     +move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ?.
      apply ltnW.
      rewrite -subn1 -2!addn1 subnK; last apply positivity_w => //.
      by rewrite addn1.
      
   *move/eqP => wr; move/eqP => wl ic /=.
    rewrite /= size_cat size_delete -wr -wl; last first.
     move: sc; rewrite /leq -subSn.
     rewrite -wl -wr -subnDA //.
     move: (leq_total (w ^ 2)./2 i).
     rewrite wl; move/orP => [] //.
     rewrite leq_eqVlt ic orbF.
     move/eqP => -> //.
    apply/andP; split; first apply leq_addr.
    rewrite -subn1 addnBA // -addn1 subnK; last apply ltn_addr => //.
    rewrite -addnn leq_add // -divn2 leq_div //.
    
   *move=> wr; move/eqP => wl ic /=.
    rewrite !eq_refl /= wl /= size_delete; last first.
     move: sc; rewrite /leq -subSn.
     rewrite -wl -subnDA //.
     move: (leq_total (w ^ 2)./2 i).
     rewrite wl; move/orP => [] //.
     rewrite leq_eqVlt ic orbF.
     move/eqP => -> //.
    repeat (apply/andP => []; split); try by [].
     rewrite -wl -addnn -divn2 ltn_addr // trivial_lem2 //; case: w Hw => //.
    move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] H ?.
    rewrite -wl /leq -subn1 subnBA.
    move: H; rewrite !subn_eq0 addn1 leq_eqVlt wr //=.
    apply positivity_w => //.
    rewrite -addn1 -subn1 subnK; last apply positivity_w => //.
    move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? H.
    rewrite leq_eqVlt H orbT //.
    move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ? //.
    
   *move/eqP => wr; move=> wl ic /=.
    rewrite !eq_refl /= wr /= !size_delete; last first.
     rewrite /leq (@ltn_predK 0 _ _); last apply positivity_w => //. by rewrite subnn.
     move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ? //.
    move: sc; rewrite /leq -subSn.
    rewrite -subnDA //.
    move: (leq_total (size l) i).
    move/orP => [] //.
    rewrite leq_eqVlt ic orbF.
    move/eqP => -> //.
    rewrite !(@ltn_predK 0 _ _); try apply positivity_w.
    rewrite -!wr.
    repeat (apply/andP => []; split); try by (move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ?).
     move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] H ?; move/andP => [] ? ?.
     rewrite /leq -subn1 subnBA; last apply positivity_w => //.
     rewrite addn1 subn_eq0 ltn_neqAle wl /= H //.
     apply ltnW; move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ? //.
     rewrite -addnn -divn2 ltn_addr // trivial_lem2 //; case: w Hw => //.
    by rewrite wr.
    move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ? //.
     
   *move=> wr; move=> wl ic /=. 
    rewrite !eq_refl /= !size_delete; last first.
     move: sc; rewrite /leq -subSn.
     rewrite -subnDA //.
     move: (leq_total (size l) i).
     move/orP => [] //.
     rewrite leq_eqVlt ic orbF.
     move/eqP => -> //.
    repeat (apply/andP => []; split); try by (move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? ?).
     move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] H ?.
     move: (H); rewrite leq_eqVlt wr /= /leq => H'.
     rewrite -subn1 subnBA; last apply positivity_w => //.
     rewrite addn1 //.
    move/andP: wfB => [] ?; move/andP => [] ?; move/andP => []; move/andP => [] ? ?; move/andP => [] ? H.
    apply ltnW; rewrite (@ltn_predK 0 _ _) //; apply positivity_w => //.
    
  -move/andP=>[];move/eqP=>H; by move: H n_gt0 => ->.
    
  -move/andP=>[]?? sc.
   move/andP=>[];rewrite size_cat;move/eqP=>H wfl.
   apply balanceL'_wf; last by decomp wfl.
   apply dellvs_wf; decomp wfl; rewrite // -H //.
    
  -move/andP=>[]?? sc.
   move/andP=>[];rewrite size_cat;move/eqP=>H wfl.
   apply balanceR'_wf; last by decomp wfl.
   apply dellvs_wf; decomp wfl => //.
   rewrite /leq -addn1 !subnDA -!subnBA; last rewrite positivity_w //.
   rewrite -!subnDA !addnA !addnBA; last rewrite positivity_w //.
   rewrite /leq -addn1 -subnBA in sc; last rewrite !ltn_addr // positivity_w //.
   rewrite addnC -addnBA addnC // in sc; last rewrite !ltn_addr // positivity_w //.
    
  -move/andP=>[]?? sc wfl.
   apply balanceL'_wf; last by decomp wfl.
   apply dellvs_wf; decomp wfl => //.
   move/eqP: H; move/eqP: H3 => <- <- //.
    
  -move/andP=>[]?? sc wfl.
   apply balanceR'_wf; last by decomp wfl.
   apply dellvs_wf; decomp wfl => //.
   rewrite /leq -addn1 !subnDA -!subnBA; last rewrite positivity_w //.
   rewrite -!subnDA !addnA !addnBA; last rewrite positivity_w //.
   rewrite /leq -addn1 -subnBA in sc; last rewrite !ltn_addr // positivity_w //.
   rewrite addnA addnC -addnBA addnC // in sc; last rewrite !ltn_addr // positivity_w //.
    
  -move/andP => []; move/andP => [] ?; move/andP => []; move/andP => [] n1_gt0 rbll rblr; move/andP => [] rbrl rbrr sc wfB.
   apply balanceL'_wf;
   move/andP: wfB => []; move/eqP => H; move/andP => [] ?; move/andP => []; move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ?;
   move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ? => //.
   apply (IHd _ n1_gt0).
    by rewrite /= n1_gt0 rbll rblr rbrl.
    move: H; rewrite size_cat -!dsizeE //= => H; by apply ltn_addr; rewrite -H.
    rewrite /= !size_cat !count_cat !dsizeE // !donesE // !eq_refl; repeat (apply/andP; split => //).
    
  -move/andP => []; move/andP => [] ?; move/andP => []; move/andP => [] n1_gt0 rbll rblr; move/andP => [] rbrl rbrr sc wfB.
   apply balanceR'_wf;
   move/andP: wfB => []; move/eqP => H; move/andP => [] ?; move/andP => []; move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ?;
   move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ? => //.
   apply (IHd _ n1_gt0).
    by rewrite /= rbrl rbrr.
    move: H sc; rewrite size_cat -!dsizeE //= => H.
    rewrite H /leq => sc.
    rewrite -subSn; last first.
     rewrite -H leqNgt.
     apply/implyP => H'.
     by rewrite H' in y.
    rewrite -subnDA //.
    repeat (apply/andP; split => //).
    repeat (apply/andP; split => //).
     
 -move/andP => []; move/andP => [] ?; move/andP => [] rbll rblr; move/andP => []; move/andP => [] n1_gt0 rbrl rbrr sc wfB.
  apply balanceL'_wf;
  move/andP: wfB => []; move/eqP => H; move/andP => [] ?; move/andP => []; move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ?;
  move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ? => //.
  apply (IHd _ n1_gt0).
   by rewrite /= rbll rblr.
   move: H; by rewrite size_cat -!dsizeE //= => <-.
   repeat (apply/andP; split => //).
   repeat (apply/andP; split => //).
   
 -move/andP => []; move/andP => [] ?; move/andP => [] rbll rblr; move/andP => []; move/andP => [] n1_gt0 rbrl rbrr sc wfB.
  apply balanceR'_wf;
  move/andP: wfB => []; move/eqP => H'; move/andP => [] ?; move/andP => []; move/andP => []; move/eqP => H; move/andP => [] ?; move/andP => [] ? ?;
  move/andP => [] ?; move/andP => [] ?; move/andP => [] ? ? => //.
  apply (IHd _ n1_gt0).
   by rewrite /= n1_gt0 rblr rbrl rbrr.
   move: H sc; rewrite -!dsizeE //= => H.
   rewrite H /leq !addnA -subSn; last first.
    rewrite !dsizeE // leqNgt.
    apply/implyP => H''.
    rewrite size_cat in H'.
    move: H' (ltn_addr (size (dflatten lr)) H'') => <- H'.
    by rewrite H' in y.
   by rewrite -subnDA !addnA //.
   rewrite /= !dsizeE // !donesE //; repeat (apply/andP; split => //).
     
  -case: c y => // y; move/andP => [] rbl rbr sc. 
   move/andP => []; move/eqP => H; move/andP => [] ?; move/andP => [] wfl wfr.
   apply balanceL'_wf => //.
    apply (IHd n) => //.
    by apply is_redblack_Red_Black.
    by rewrite dsizeE // -H.
   move/andP: rbl => [] _ rbl.
   move/andP => []; move/eqP => H; move/andP => [] los; move/andP => [] wfl wfr.
   case: n n_gt0 rbl rbr => // n; case neq: n => /= n_gt0.
    move: l y sc wfl IHd H los => /= [[]//ll[]?? lr|?] //; move: r wfr => [[]//rl[]?? rr|?] //;
    try move:ll lr =>[[]//|?] [[]//|?] //=;
    try move:rl rr =>[[]//|?] [[]//|?] //=;
    rewrite !size_cat //= => wfr _ ? wfl ? H ? _ _;
    rewrite balanceL'_wf // ddel0E dellvs_wf //; first rewrite -H //;
    move/andP:wfl=>[]?;move/andP=>[]?;move/andP=>[]?;move/andP=>[]?//.
   move=>rbl rbr; rewrite balanceL'_wf // (IHd n) //; last rewrite dsizeE // -H //; rewrite neq //.
    
  -case: c y => // y; move/andP => [] rbl rbr sc;
   move/andP => []; move/eqP => H; move/andP => [] los; move/andP => [] wfl wfr;
   have scm: i - dsize l < dsize r
    by (rewrite /leq -addn1 -!subnBA; last rewrite positivity //;
    rewrite -!subnDA addnBA; last rewrite positivity //;
    rewrite /leq -addn1 -subnBA // in sc; last rewrite !ltn_addr // positivity //).
   move:y0;case:ifP=>// y0 _.
   apply balanceR'_wf => //.
    apply (IHd n) => //{IHd}.
    by apply is_redblack_Red_Black.
    by rewrite H -dsizeE //.
   move/andP: rbl => [] _ rbl.
   
   case: n n_gt0 rbl rbr => // n; case neq: n => /= n_gt0.
    move: l y sc wfl IHd H los scm => /= [[]//ll[]?? lr|?] //; move: r wfr => [[]//rl[]?? rr|?] //;
    try move:ll lr =>[[]//|?] [[]//|?] //=;
    try move:rl rr =>[[]//|?] [[]//|?] //=;
    rewrite !size_cat //= => wfr _ sc wfl ? H ? scm  _ _;
    rewrite balanceR'_wf // ddel0E dellvs_wf //;
    try by rewrite H //.
    (* by decomp wfr. *)
    all: try by decomp wfr.
   move=>rbl rbr; rewrite balanceR'_wf // (IHd n) //; try by rewrite neq //.
   rewrite H // -dsizeE //.
  -move/eqP=>C;move:n_gt0; rewrite C //.
Qed.

End delete.

End dtree.
