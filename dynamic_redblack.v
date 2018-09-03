From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete set_clear.

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
Proof. move; case; case => /=; try apply ReflectT => //; try apply ReflectF => //. Qed.

Canonical color_eqMixin := EqMixin color_eqP.
Canonical color_eqType := Eval hnf in EqType color color_eqMixin.

Fixpoint eq_dtree (t1 t2 : dtree) := 
  match t1,t2 with
  | Bleaf a,Bleaf b => a == b
  | Bnode c1 l1 d1 r1,Bnode c2 l2 d2 r2 => (d1 == d2) && (c1 == c2) && (eq_dtree l1 l2) && (eq_dtree r1 r2)
  | Bnode _ _ _ _,Bleaf _ 
  | Bleaf _,Bnode _ _ _ _ => false
  end.

Lemma eq_dtree_ref (t : dtree) : eq_dtree t t.
Proof. elim t => [? l H1 ? r H2 /=|a //=]; by rewrite H1 H2 !eq_refl. Qed.

Lemma eq_dtree_iff t1 t2 : t1 = t2 <-> eq_dtree t1 t2.
Proof.
  split => [->|]; first by rewrite eq_dtree_ref.
  move: t1 t2; elim => [? l1 lH1 ? r1 rH1|?]; elim => [? l2 lH2 ? r2 rH2 H|?] //;last by move/eqP => /= ->.
  move/andP: H; case; move/andP; case; move/andP; case; move/eqP => ->; move/eqP => -> H1 H2.
  by rewrite (lH1 _ H1) (rH1 _ H2).
Qed.

Lemma dtree_eqP : Equality.axiom eq_dtree.
Proof.
  move; case => [? l1 ? r1 |?]; case => [? l2 ? r2|?] //; set b:= (eq_dtree _ _); case Hb : b; subst b; try (apply ReflectT; apply eq_dtree_iff => //); try apply ReflectF => //.
   by case => H1 H2 H3 H4; move: Hb; rewrite H1 H2 H3 H4 eq_dtree_ref.
  by case => H1; move: Hb; rewrite H1 eq_dtree_ref.
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
    apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr b i] /=.
      case: ifP => Hi. by apply: balanceL_wf.
      by apply: balanceR_wf.
    move => s Hs b i //=.
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

  Lemma dinsert_is_redblack' (B : dtree) b i n :
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
    apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi].
      rewrite -dsizeE //.
      case: ifP => Hil.
        case_eq (bset l i) => l' b Hbset /=.
        by rewrite addnAC -IHl // Hbset.
      case_eq (bset r (i - dsize l)) => r' b Hbset /=.
      rewrite -addnA -IHr ?Hbset //.
      by rewrite -(ltn_add2l (dsize l)) subnKC // leqNgt Hil.
    move => s Hs i Hi; by rewrite addnC -count_bit_set.
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
    apply: dtree_ind => //= [c l r num ones -> -> [wfl wfr] IHl IHr i /= Hi].
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
    move => s Hs i Hi; by rewrite -count_bit_clear.
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

(* Deletion: work in progress *)
Section delete.

  Inductive near_dtree: Type :=
  | Stay : dtree -> near_dtree
  | Down : dtree -> near_dtree.

  Definition balanceL2 col (l : near_dtree) (r : dtree) : near_dtree :=
    match l with
    | Stay l => Stay (rbnode col l r)
    | Down l =>
      match col,r with
      | _, Bnode _ (Bnode Red rll _ rlr) _ rr => Stay (rbnode col (bnode l rll) (bnode rlr rr))
      | Black,Bnode Red (Bnode Black (Bnode Black _ _ _ as rll) _ rlr) _ rr
      | Black,Bnode Red (Bnode Black (Bleaf _ as rll) _ rlr) _ rr =>
        Stay (bnode (bnode (rnode l rll) rlr) rr)
      | Black,Bnode Red (Bnode Black (Bnode Red rlll _ rllr) _ rlr) _ rr =>
        Stay (bnode (bnode l rlll) (rnode (bnode rllr rlr) rr))
      | Black,Bnode Black (Bnode Black _ _ _ as rl) _ rr =>
        Down (bnode (rnode l rl) rr)
        (* absurd case *)
      | _,_ => Stay (rbnode col l r)
      end
    end.

  Definition balanceR2 col (l : dtree) (r : near_dtree) : near_dtree :=
    match r with
    | Stay r => Stay (rbnode col l r)
    | Down r =>
      match col,l with
      | _, Bnode _ ll _ (Bnode Red lrl _ lrr) => Stay (rbnode col (bnode ll lrl) (bnode lrr r))
      | Black,Bnode Red ll _ (Bnode Black lrl _ (Bnode Black _ _ _ as lrr))
      | Black,Bnode Red ll _ (Bnode Black lrl _ (Bleaf _ as lrr)) =>
        Stay (bnode ll (bnode lrl (rnode lrr r)))
      | Black,Bnode Red ll _ (Bnode Black lrl _ (Bnode Red lrrl _ lrrr)) =>
        Stay (bnode (rnode ll (bnode lrl lrrl)) (bnode lrrr r))
      | Black,Bnode Black ll _ (Bnode Black _ _ _ as lr) =>
        Down (bnode ll (rnode lr r))
        (* absurd case *)
      | _,_ => Stay (rbnode col l r)
      end
    end.

  Definition delete_leaves2 p l r (i : nat) : dtree :=
    if i < size l
    then match p,w ^ 2 %/ 2 == size l,w ^ 2 %/2 == size r with
         | _,true,true =>
           leaf ((rcons (delete l i) (access r 0)) ++ (delete r 0))
         | c,true,false => 
           rbnode c (leaf (rcons (delete l i) (access r 0))) (leaf (delete r 0))
         | c,false,_ => 
           rbnode c (leaf (delete l i)) (leaf r)
         end
    else match p,w ^ 2 %/ 2 == size l,w ^ 2 %/2 == size r with
         | _,true,true =>
           leaf (l ++ (delete r (i - (size l))))
         | c,false,true => 
           rbnode c (leaf (delete l (size l).-1)) (leaf ((access l (size l).-1) :: (delete r (i - size l))))
         | c,_,false => 
           rbnode c (leaf l) (leaf (delete r (i - (size l))))
         end.

  Fixpoint height_of_dtree (B : dtree) :=
    match B with
    | Bnode Black l _ r => (maxn (height_of_dtree l) (height_of_dtree r)).+2
    | Bnode Red l _ r => (maxn (height_of_dtree l) (height_of_dtree r)).+1
    | Bleaf _ => 0
    end.

  Lemma pigeonhole_principle a b : a < b -> b < a.+1 -> false.
  Proof. rewrite leq_eqVlt; move/orP; case; [ move/eqP => <- | move => H1 H2; move: (ltn_trans H1 H2) ]; by rewrite ltnn. Qed.

  Lemma ltn_trans1 (l m n : nat) : l < m -> m < n.+1 -> l < n.
  Proof. move => H1; case: leqP => // H2 ?; exact (leq_trans H1 H2). Qed.

  Lemma hc_pcl {l r c s n} : height_of_dtree l < height_of_dtree (Bnode c l (s, n) r).
  Proof. case c; rewrite /= -!maxnSS leq_max ltnS; [ rewrite leqnn // | rewrite ltnW // ]. Qed.

  Lemma hc_pcr {l r c s n} : height_of_dtree r < height_of_dtree (Bnode c l (s, n) r).
  Proof. case c; rewrite /= -!maxnSS leq_max ltnS; [ rewrite leqnn orbT // | apply/orP; apply or_intror; rewrite ltnW // ]. Qed.

  Lemma hc_pcl' {lr ll r s p n} : height_of_dtree (rnode lr r) < height_of_dtree (Bnode Black (Bnode Red ll p lr) (s, n) r).
  Proof. rewrite /= -!maxnSS -maxnA !leq_max !/maxn; case: ifP => H; [ rewrite ltnSn !orbT // | rewrite [ _.+1 < (_ lr).+3]ltnW // orbT // ]. Qed.

  Lemma hc_pcr' {l rl rr s n p} : height_of_dtree (rnode l rl) < height_of_dtree (Bnode Black l (s, n) (Bnode Red rl p rr)).
  Proof. rewrite /= -!maxnSS maxnA !leq_max !/maxn; case: ifP => H; [ rewrite [ _.+1 < (_ rl).+3]ltnW // orbT // | rewrite ltnSn // ]. Qed.

  Lemma wf_hc' : forall B, (forall B', height_of_dtree B' < height_of_dtree B -> Acc (fun B B' => height_of_dtree B < height_of_dtree B') B').
  Proof.
    elim => [[] l IH1 d r IH2|?] B' /=; last (by rewrite ltn0); move: B' => [/= [] x1 ? ? H1 |? ? /=]; apply Acc_intro => x2; try (by rewrite ltn0);
    try (move => H2; move:(ltn_trans1 H2 H1); rewrite /maxn; case: ifP => ? H3; [ apply (IH2 _ H3) | apply (IH1 _ H3) ]);
    try (move => H2; apply Acc_intro => x3 H3; move:(ltn_trans1 H3 (ltn_trans1 H2 H1)); rewrite /maxn; case: ifP => ? H4; [ apply (IH2 _ H4) | apply (IH1 _ H4) ]).
  Qed.

  Lemma wf_hc : well_founded (fun B B' => height_of_dtree B < height_of_dtree B').
  Proof. move => ?; apply Acc_intro; apply wf_hc'. Qed.

  Function ddelete (B : dtree) (i : nat) { measure height_of_dtree B } : near_dtree :=
    match B  with
    | Bnode Black (Bleaf l) _ (Bleaf r) => Down (delete_leaves2 Black l r i)
    | Bnode Red (Bleaf l) _ (Bleaf r) => Stay (delete_leaves2 Red l r i)
    | Bnode Black (Bnode Red (Bleaf ll) _ (Bleaf lr)) (s,_) (Bleaf r) =>
      if i < s
      then Stay (bnode (delete_leaves2 Red ll lr i) (leaf r))
      else Stay (bnode (leaf ll) (delete_leaves2 Red lr r (i - (size ll))))
    | Bnode Black (Bleaf l) (s,_) (Bnode Red (Bleaf rl) _ (Bleaf rr)) =>
      if i < s
      then Stay (bnode (delete_leaves2 Red l rl i) (leaf rr))
      else Stay (bnode (leaf l) (delete_leaves2 Red rl rr (i - s)))
    | Bnode Black (Bnode Black _ _ _ as l) (s,_) (Bnode Red rl _ rr as r) =>
      if i < s
      then balanceL2 Black (ddelete (rnode l rl) i) rr
      else balanceR2 Black l (ddelete r (i - s))
    | Bnode Black (Bnode Red ll _ lr as l) (s,_) (Bnode Black _ _ _ as r) =>
      if i < s
      then  balanceL2 Black (ddelete l i) r
      else balanceR2 Black ll (ddelete (rnode lr r) i)
    | Bnode c l (s,_) r => 
      if i < s
      then balanceL2 c (ddelete l i) r
      else  balanceR2 c l (ddelete r (i - s))
    (* absurd case *)
    | Bleaf _ =>  Stay B
    end.

  subst B. try (apply/eqP; rewrite /= subSS; apply/eqP; try (by apply leq_maxl); by apply leq_maxr); try (apply hc_pcl); try (apply hc_pcr); last (apply hc_pcr'); apply hc_pcl'. 


  Definition ddelete (B : dtree) (i : nat) : near_dtree.

    move: B i.
    refine (Fix wf_hc (fun _ => _) _) => B ddelete i.
    refine (
        match B as tr return B = tr -> near_dtree with
        | Bnode Black (Bleaf l) _ (Bleaf r) => fun _ => Down (delete_leaves2 Black l r i)
        | Bnode Red (Bleaf l) _ (Bleaf r) => fun _ => Stay (delete_leaves2 Red l r i)
        | Bnode Black (Bnode Red (Bleaf ll) _ (Bleaf lr)) (s,_) (Bleaf r) =>
          if i < s
          then fun _ => Stay (bnode (delete_leaves2 Red ll lr i) (leaf r))
          else fun _ => Stay (bnode (leaf ll) (delete_leaves2 Red lr r (i - (size ll))))
        | Bnode Black (Bleaf l) (s,_) (Bnode Red (Bleaf rl) _ (Bleaf rr)) =>
          if i < s
          then fun _ => Stay (bnode (delete_leaves2 Red l rl i) (leaf rr))
          else fun _ => Stay (bnode (leaf l) (delete_leaves2 Red rl rr (i - s)))
        | Bnode Black (Bnode Black _ _ _ as l) (s,_) (Bnode Red rl _ rr as r) =>
          if i < s
          then fun (_ : B = (Bnode Black l _ (Bnode Red rl _ rr))) => balanceL2 Black (ddelete (rnode l rl) _ i) rr
          else fun (_ : B = (Bnode Black l _ r)) => balanceR2 Black l (ddelete r _ (i - s))
        | Bnode Black (Bnode Red ll _ lr as l) (s,_) (Bnode Black _ _ _ as r) =>
          if i < s
          then fun (_ : B = (Bnode Black l _ r)) => balanceL2 Black (ddelete l _ i) r
          else fun (_ : B = (Bnode Black (Bnode Red ll _ lr) _ r)) => balanceR2 Black ll (ddelete (rnode lr r) _ i)
        | Bnode c l (s,_) r => 
          if i < s
          then fun (_ : B = (Bnode c l _ r)) => balanceL2 c (ddelete l _ i) r
          else fun (_ : B = (Bnode c l _ r)) => balanceR2 c l (ddelete r _ (i - s))
        (* absurd case *)
        | Bleaf _ => fun _ => Stay B
        end erefl
      ); subst B; try (apply/eqP; rewrite /= subSS; apply/eqP; try (by apply leq_maxl); by apply leq_maxr); try (apply hc_pcl); try (apply hc_pcr); last (apply hc_pcr'); apply hc_pcl'. 
  Defined.

  Fixpoint dflattenn tr :=
    match tr with
    | Stay t => dflatten t
    | Down t => dflatten t
    end.

  Lemma balanceL2E c l r : dflattenn (balanceL2 c l r) = dflattenn l ++ dflatten r.
  Proof.
    move: l => [] ?; case c; case r => [] [] // [] //= [] [] [] /=; intros; rewrite //= -!catA //= -!catA //.
  Qed.

  Lemma balanceR2E c l r : dflattenn (balanceR2 c l r) = dflatten l ++ dflattenn r.
  Proof.
    move: r => [] ?; case c; case l => //= [c'] ? ? [c''|]; try case c'; try case c''; try (intros; rewrite //= -!catA //= -!catA //=);
    move => ? ? [] x; first case x; intros; rewrite //= -!catA //= -!catA //=.
  Qed.

  Lemma ddeleteE (B : dtree) i :
    wf_dtree B -> dflattenn (ddelete B i) = delete (dflatten B) i.
  Proof.
    move => wf. rewrite /ddelete. move: B wf i. apply: dtree_ind.
    move => c l r ? ? ? ? [] wfl wfr IHl IHr i.
    rewrite /ddelete /dflattenn /=.
    move: IHl IHr; case c; case l; case r.

    rewrite /Fix /Fix_F /dflattenn.
    
    destruct wf_hc.
    destruct Acc.
    compute.
    rewrite /=.
    rewrite /=.
    destruct Fix.
    rewrite /=.

    compute.
    + move => c l r num ones Hnum Hones _ IHl IHr /= b i.
      case: ifPn => ?.
      - by rewrite balanceLE IHl /insert1 insert_catL -?Hnum.
      - by rewrite balanceRE IHr /insert1 insert_catR -?Hnum // leqNgt.
    + move => s Hs b i.
      rewrite /dins. case: ifP => Hi //.
      by rewrite dflatten_node /dflatten cat_take_drop.
  Qed.
  Proof. move => wf. rewrite /dinsert -(dinsE b i wf). by case: dins. Qed.

  Definition delete_leaf s i uf :=
    if (size s == (w^2) %/ 2) && ~~uf
    then (s, None)
    else (delete s i, Some (nth true s i)).

  (* s = size C, o = rank C *)
  Fixpoint insw B i (C : seq bool) s o :=
    match B with
    | Bnode c l (num, ones) r =>
      if i <= num
      then Bnode c (insw l i C s o) (num + s, ones + o) r
      else Bnode c l (num, ones) (insw r (i - num) C s o)
    | Bleaf s => (Bleaf _ (insert s C i))
    end.

  Lemma inswE B i (C : seq bool) s o :
    wf_dtree B -> dflatten (insw B i C s o) = insert (dflatten B) C i.
  Proof.
    move=> wf; move: B wf i C s o.
    apply: dtree_ind => // c l r num ones -> -> _ IHl IHr i C s o /=.
    case: ifP => Hi //=; try rewrite IHl; try rewrite IHr;
      rewrite /insert; rewrite take_cat drop_cat; rewrite ltn_neqAle;
      rewrite Hi ?andbT ?andbF -!catA //.
    case Heq: (i == size (dflatten l)) => //=.
    by rewrite (eqP Heq) subnn take0 drop0 take_size drop_size !cats0.
  Qed.

  Fixpoint del_head B : (dtree * option bool) :=
    match B with
    | Bleaf s => match s with
                 | [::] => (B, None)
                 | h :: t => (Bleaf _ t, Some h)
                 end
    | Bnode c l (num, ones) r =>
      let (l', opt_b) := del_head l in
      if opt_b is Some b' then (Bnode c l' (num - 1, ones - b') r, opt_b) else
      let (r', opt_b') := del_head r in (Bnode c l (num, ones) r', opt_b')
    end.

  Lemma behead_cat T (s t : seq T) : size s != 0 ->
    behead (s ++ t) = (behead s) ++ t.
  Proof. by elim: s. Qed.

  Lemma dsizeP B : wf_dtree B -> reflect (dsize B = 0) (nilp (dflatten B)).
  Proof.
    move=> wf; rewrite dsizeE //; apply /eqP.
  Qed.

  Lemma del_head_nonempty B x : (del_head B).2 = Some x ->
    size (dflatten B) != 0.
  Proof.
    elim: B => [c l IHl [num ones] r IHr | []] //=.
    case: (del_head l) IHl => l' /= [b Hb /Hb | _].
      by rewrite size_cat addn_eq0 negb_and => ->.
    case: (del_head r) IHr => r' [b Hb /Hb|] //=.
    by rewrite size_cat addn_eq0 negb_and orbC => ->.
  Qed.

  Lemma del_head_none_isempty B : (del_head B).2 = None -> dflatten B = [::].
  Proof.
    elim: B => [c l IHl [num ones] r IHr | []] //=.
    case: (del_head l) IHl => l' [b Hb | ->] //=.
    by case: (del_head r) IHr => r' [b Hb | ->].
  Qed.

  Lemma del_headE B : wf_dtree B ->
    dflatten (del_head B).1 = behead (dflatten B).
  Proof.
    move: B; apply: dtree_ind => [c l r num ones -> -> _ IHl IHr | []] //=.
    rewrite (surjective_pairing (del_head l)).
    case Hb: (del_head l).2 => /=.
      by rewrite IHl behead_cat // (del_head_nonempty Hb).
    rewrite (surjective_pairing (del_head r)) /=.
    by rewrite IHr (del_head_none_isempty Hb).
  Qed.

  Fixpoint del_last B : (dtree * option bool) :=
    match B with
    | Bleaf s => match s with
                 | [::] => (B, None)
                 | h :: t => (Bleaf _ (belast h t), Some (last h t))
                 end
    | Bnode c l (num, ones) r =>
      let (r', opt_b) := del_last r in
      if opt_b is Some b then (Bnode c l (num, ones) r', Some b) else
      let (l', opt_b') := del_last l in
      if opt_b' is Some b' then (Bnode c l' (num - 1, ones - b') r, Some b')
                           else (Bnode c l (0, 0) r, None)
    end.

  Definition belast' T (s : seq T) := if s is x :: s' then belast x s' else [::].
  Lemma belast'_belast T x (s : seq T) : size s != 0 ->
    belast x s = x :: (belast' s).
  Proof. by elim: s. Qed.

  Lemma belast'_cat T (s t : seq T) : size t != 0 ->
    belast' (s ++ t) = s ++ (belast' t).
  Proof.
    elim: s => //= x s IHs H.
    rewrite -IHs // belast'_belast //=.
    by rewrite size_cat addn_eq0 negb_and H orbT.
  Qed.

  Lemma del_last_nonempty B x : (del_last B).2 = Some x ->
    size (dflatten B) != 0.
  Proof.
    elim: B => [c l IHl [num ones] r IHr | []] //=.
    case: (del_last r) IHr => r' /= [b Hb /Hb | _].
      by rewrite size_cat addn_eq0 negb_and orbC => ->.
    case: (del_last l) IHl => l' /= [b Hb /Hb | _ ] //.
    by rewrite size_cat addn_eq0 negb_and => ->.
  Qed.

  Lemma del_last_none_isempty B : (del_last B).2 = None -> dflatten B = [::].
  Proof.
    elim: B => [c l IHl [num ones] r IHr | []] //=.
    case: (del_last r) IHr => r' [b Hb | ->] //=.
    by case: (del_last l) IHl => l' [b Hb | ->].
  Qed.

  Lemma del_lastE B : wf_dtree B ->
    dflatten (del_last B).1 = belast' (dflatten B).
  Proof.
    move: B; apply: dtree_ind => [c l r num ones -> -> _ IHl IHr | []] //=.
    rewrite (surjective_pairing (del_last r)).
    case Hb: (del_last r).2 => /=.
      by rewrite IHr belast'_cat // (del_last_nonempty Hb).
    rewrite (surjective_pairing (del_last l)).
    case Hb': (del_last l).2 => /=.
      by rewrite (del_last_none_isempty Hb) !cats0.
    by rewrite !del_last_none_isempty.
  Qed.

  Lemma del_last2E B x0 : wf_dtree B -> dsize B > 0 ->
    (del_last B).2 = Some (last x0 (dflatten B)).
  Proof.
    move=> wf; move: B wf x0.
    apply: dtree_ind => [c l r num ones -> -> [wfl wfr] IHl IHr x0 | []] //=.
    rewrite (surjective_pairing (del_last r)).
    case Hb: (del_last r).2 => /=.
      by rewrite -Hb last_cat -IHr // dsizeE // lt0n (del_last_nonempty Hb).
    rewrite (dsizeE wfr) /= (del_last_none_isempty Hb) cats0 addn0 => Hsize.
    rewrite (surjective_pairing (del_last l)).
    case Hb': (del_last l).2 => /=.
      by rewrite -IHl // Hb'.
    by rewrite (dsizeE wfl) (del_last_none_isempty Hb') in Hsize.
  Qed.

  Definition redden (B : dtree) :=
    match B with
    | Bnode _ l (num, ones) r => Bnode Red l (num, ones) r
    | _ => B
    end.

  Definition bal_left (l r : dtree) :=
    match l, r with
    | Bnode Red a (na, oa) b, c => Bnode Red (Bnode Black a (na, oa) b)
                                         (dsize l, drank_size l) c
    | bl, Bnode Black a (na, oa) b => balanceR Black l (Bnode Red a (na, oa) b)
    | bl, Bnode Red (Bnode Black a (na, oa) b) _ c => Bnode Red (Bnode Black bl (dsize bl, drank_size bl) a) (dsize bl + na, drank_size bl + oa) (balanceR Black b (redden c))
    | _, _ => Bnode Red l (dsize l, drank_size l) r
    end.

  Fixpoint bdel B i w uf : (dtree * option bool) :=
    match B with
    | Bleaf s => let (s, b) := delete_leaf s i uf
                 in (Bleaf _ s, b)
    | Bnode c l (num, ones) r as v =>
      if i <= num
      then let (l', opt_b) := bdel l i w uf
           in match opt_b with
              | None => (v, None)
              | Some b => if num == (w ^ 2) %/ 2
                          then let (r', opt_b') := del_head r
                               in match opt_b' with
                                  | None => (* merge leaves *)
                                    (insw r' 0 (dflatten l') (w ^ 2 - 1)
                                          (ones - b), opt_b)
                                  | Some b' =>
                                    let l'_i := dinsert l' b' ((w^2) %/ 2)
                                    in match l'_i with
                                       | Bnode Black _ _ _ =>
                                      (bal_left l'_i r', opt_b)
                                       | _ => (Bnode Red l'_i (dsize l'_i, drank_size l'_i) r, opt_b)
                                       end
                                  end
                          else (Bnode c l' (num - 1, ones - b) r, opt_b)
              end
      else let o := drank_size B
           in let (r', opt_b) := bdel r (i - num) w uf
           in match opt_b with
              | None => (v, None)
              | Some b => if (dsize B) - num == (w ^ 2) %/ 2
                          then let (l', opt_b') := del_last l
                               in match opt_b' with
                                  | None =>
                                    (insw l' (num + 1) (dflatten r')
                                         ((w ^ 2) - 1) (o - b - ones),
                                     opt_b)
                                  | Some b' =>
                                    (balanceL c (dinsert r' b' 1)
                                              r', opt_b)
                                  end
                          else (Bnode c l (num, ones) r', opt_b)
              end
    end.

(*
  Definition ddelete B i w := (bdel B i (drank_size B) w true).1.

  Definition ddeleteE B i w :
    wf_dtree B -> dflatten (ddelete B i w) = delete (dflatten B) i.
  Proof.
    move=> wf; move: B wf i w; rewrite /ddelete. apply: dtree_ind => //=.
    move=> c l r num ones -> -> _ IHl IHr //= i w.
    case: ifP => Hi.
    case_eq (bdel l i ((count_mem true) (dflatten l)) w true) => l' [b Hl'|] //=.
    rewrite Hl'. case: eqP => Hw.
    case_eq (bdel r 0 0 w false) => r' [b' Hr'|] //=.
    rewrite balanceRE. rewrite dinsertE.
*)

End delete.

End dtree.