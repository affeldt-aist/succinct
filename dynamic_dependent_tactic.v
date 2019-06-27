From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import Program JMeq Compare_dec ExtrOcamlNatInt.
Require Import tree_traversal rank_select insert_delete set_clear dynamic.

Set Implicit Arguments.

Tactic Notation "remember_eq" constr(expr) ident(vname) ident(eqname) := case (exist (fun x => x = expr) expr erefl) => vname eqname.

Section dynamic_dependent.
Variable w : nat.
Hypothesis wordsize_gt1: w > 1.

Section insert.

  Definition balanceL {nl ml d cl cr nr mr} (p : color) (l : near_tree w nl ml d cl) (r : tree w nr mr d cr) :
    color_ok p (fix_color l) (* important claim! *) ->
    color_ok p cr ->
    {tr : near_tree w (nl + nr) (ml + mr) (incr_black d p) p | dflatteni tr = dflatteni l ++ dflatten r}.

    destruct l as [s1 o1 s2 o2 s3 o3 d' x y z | s o d' c' cc l'].
    (* l is bad *)
    + case: p => //= cpl cpr.
      rewrite -(addnA (s1 + s2)) -(addnA (o1 + o2)).
      exists (Good Black (rnode (bnode x y) (bnode z r))).
      by rewrite /= !catA.
    (* l is good *)
    + case: p => /= cpl cpr; last by exists (Good Black (bnode l' r)).
      case Hc': c' in cpl.
      (* bad pattern (c' and p are red) *)
      - destruct l' as [|s1 o1 s2 o2 d cl' cr' c' w1 w2 l'1 l'2] => //.
        subst c'; destruct cl', cr', cr => //.
        exists (Bad l'1 l'2 r).
        by rewrite /= !catA.
      (* otherwise *)
      - subst c'; destruct cr => //.
        by exists (Good Red (rnode l' r)).
  Defined.

  Definition balanceR {nl ml d cl cr nr mr} (p : color) (l : tree w nl ml d cl) (r : near_tree w nr mr d cr):
    color_ok p cl ->
    color_ok p (fix_color r) ->  (* important claim! *)
    {tr : near_tree w (nl + nr) (ml + mr) (incr_black d p) p | dflatteni tr = dflatten l ++ dflatteni r}.

    destruct r as [s1 o1 s2 o2 s3 o3 d' x y z | s o d' c' cc r'].
    (* r is bad *)
    + case: p => //= cpl cpr.
      rewrite -!addnA [nl + (s1 + (s2 + s3))]addnA [ml + (o1 + (o2 + o3))]addnA.
      exists (Good Black (rnode (bnode l x) (bnode y z))).
      by rewrite /= !catA.
    (* r is good *)
    + case: p => /= cpl cpr; last by exists (Good Black (bnode l r')).
      case Hc': c' in cpr.
      (* bad pattern (c' and p are red) *)
      - destruct r' as [|s1 o1 s2 o2 d cl' cr' c' w1 w2 r'1 r'2] => //=.
        subst c'; destruct cl', cr', cl => //.
        rewrite !addnA.
        by exists (Bad l r'1 r'2).
      (* otherwise *)
      - subst c'; destruct cl => //.
        by exists (Good Red (rnode l r')).
  Defined.

  Program Fixpoint dinsert' {n m d c} (B : tree w n m d c) (b : bool) i
          {measure (size_of_tree B)} : { B' : near_tree w n.+1 (m + b) d c
                              | dflatteni B' = insert1 (dflatten B) b i } :=
    match B with
    | Leaf s _ _ =>
      let s' := insert1 s b i in
      match size s' == 2 * (w ^ 2) with
      | true => let n  := (size s') %/ 2 in
                let sl := take n s' in
                let sr := drop n s' in
                Good c (rnode (Leaf _ sl _ _) (Leaf _ sr _ _))
      | false => Good c (Leaf _ s' _ _)
      end
    | Node s1 o1 s2 o2 d cl cr _ okl okr l r =>
      if i < s1
      then proj1_sig (balanceL c (dinsert' l b i) r _ okr)
      else proj1_sig (balanceR c l (dinsert' r b (i - s1)) okl _)
    end.

  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_take size_insert1.
    move => H.
    rewrite H.
    case: ifP => H2. by rewrite mulKn // leq_div //.
    have H3 : w ^ 2 %/ 2 <= w ^ 2. by rewrite leq_div.
    have H4 : w ^ 2 <= 2 * w ^ 2. by rewrite leq_pmull.
    by move:(leq_trans H3 H4).
  Qed.

  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_take size_insert1.
    move => H.
    rewrite H mulnC.
    case: ifP => //.
    rewrite mulnK //.
    have H2 : w ^ 2 > 0. by rewrite expn_gt0 wordsize_gt0.
    have H3 : w ^ 2 < w ^ 2 * 2. by rewrite -{1}[w ^ 2]muln1 ltn_mul2l H2 /=.
    by rewrite H3.
  Qed.

  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_drop size_insert1.
    move => H.
    by rewrite H mulKn // mulSn mul1n -addnBA // subnKC // leq_div.
  Qed.

  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_drop size_insert1.
    move => H.
    by rewrite H mulKn // mulSn mul1n -addnBA // subnKC // -{1}[w ^ 2]addn0 ltn_add2l expn_gt0 wordsize_gt0.
  Qed.

  Next Obligation. by rewrite -size_cat cat_take_drop size_insert1. Qed.

  Next Obligation.
    rewrite -count_cat cat_take_drop /count_one count_insert1.
    by destruct b.
  Qed.

  Next Obligation.
    rewrite /dflatteni /insert1.
    destruct dinsert'_func_obligation_5, dinsert'_func_obligation_6 => /=.
    by rewrite cat_take_drop.
  Qed.

  Next Obligation.
    rewrite size_insert1.
    by apply: leq_trans.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP: Heq_anonymous => /=.
    rewrite size_insert1 neq_ltn.
    case/orP => //.
    by rewrite ltnNge wildcard'0.
  Qed.

  Next Obligation. by rewrite size_insert1. Qed.

  Next Obligation. rewrite /count_one count_insert1. by destruct b. Qed.

  Next Obligation.
    rewrite /dflatteni /insert1.
    by destruct dinsert'_func_obligation_11, dinsert'_func_obligation_12, dinsert'_func_obligation_13 => /=.
  Qed.

  Next Obligation.
    apply /ltP; by rewrite -Heq_B /= -[X in X < _]addn0 ltn_add2l size_of_tree_pos.
  Qed.

  Next Obligation. by destruct dinsert',x,c. Qed.

  Next Obligation.
    apply /ltP; by rewrite -Heq_B /= -[X in X < _]add0n ltn_add2r size_of_tree_pos.
  Qed.

  Next Obligation. by destruct dinsert',x,c. Qed.

  Next Obligation. by rewrite -addn1 -[RHS]addn1 addnA. Qed.

  Next Obligation. by rewrite [o2 + b]addnC addnA. Qed.

  Next Obligation. by rewrite -[RHS]addnA [o2 + b]addnC addnA. Qed.

  Next Obligation.
    case: ifP => /= H.
    - set B' := balanceL _ _ _ _ _.
      destruct dinsert'_func_obligation_23.
      rewrite (proj2_sig B') {B'}.
      destruct dinsert' => /=.
      by rewrite e /insert1 /insert take_cat drop_cat size_dflatten H -!catA.
    - set B' := balanceR _ _ _ _ _.
      rewrite /dflatteni /eq_rect => /=.
      destruct dinsert'_func_obligation_23, dinsert'_func_obligation_22, dinsert'_func_obligation_21.
      rewrite -/(dflatteni (proj1_sig B')) (proj2_sig B') {B'}.
      destruct dinsert' => /=.
      by rewrite e /insert1 /insert take_cat drop_cat size_dflatten H -!catA.
  Qed.

  Definition dinsert n m d c (B : tree w n m d c) (b : bool) (i : nat) :=
    fix_near_tree (proj1_sig (dinsert' B b i)).

  Lemma dinsertK n m d c (B : tree w n m d c) b i :
    dflatten (dinsert B b i) = insert1 (dflatten B) b i.
  Proof. by rewrite /dinsert fix_near_treeK (proj2_sig (dinsert' B b i)). Qed.

End insert.

Section query.

  Fixpoint daccess {n m d c} (tr : tree w n m d c) i :=
    match tr with
    | Leaf s _ _ => nth false s i
    | Node lnum _ _ _ _ _ _ _ _ _ l r =>
      if i < lnum
      then daccess l i
      else daccess r (i - lnum)
    end.

  Fixpoint drank {n m d c} (tr : tree w n m d c) i :=
    match tr with
    | Leaf s _ _ => rank true i s
    | Node lnum lones rnum rones _ _ _ _ _ _ l r =>
      if i < lnum
      then drank l i
      else lones + drank r (i - lnum)
    end.

  Fixpoint dselect_0 {n m d c} (tr : tree w n m d c) i :=
    match tr with
    | Leaf s _ _ => select false i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      let zeroes := s1 - o1
      in if i <= zeroes
      then dselect_0 l i
      else s1 + dselect_0 r (i - zeroes)
    end.

  Fixpoint dselect_1 {n m d c} (tr : tree w n m d c) i :=
    match tr with
    | Leaf s _ _ => select true i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      if i <= o1
      then dselect_1 l i
      else s1 + dselect_1 r (i - o1)
    end.

  Definition access (s : seq bool) i := nth false s i.

  Lemma daccessK nums ones d c (B : tree w nums ones d c) :
    daccess B =1 access (dflatten B).
  Proof.
    rewrite /access.
    elim: B => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite nth_cat size_dflatten -IHl -IHr.
  Qed.

  Lemma drankK nums ones d c (B : tree w nums ones d c) i :
    drank B i = rank true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite rank_cat size_dflatten IHl -IHr -dflatten_rank.
  Qed.

  Lemma drank_ones num ones d c (B : tree w num ones d c) :
    drank B num = ones.
  Proof.
    by rewrite [in RHS](dflatten_rank B) drankK.
  Qed.

  Lemma dselect1K nums ones d c (B : tree w nums ones d c) i :
    dselect_1 B i = select true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_ones IHl IHr size_dflatten.
  Qed.

  Lemma dselect0K nums ones d c (B : tree w nums ones d c) i :
    dselect_0 B i = select false i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_zeroes IHl IHr size_dflatten.
  Qed.

End query.

(* Section added by Xuanrui
 * because I wanted to experiment with this version as well...
 *
 * Feel free to comment this out or remove this...
 *)

Section set_clear.

  Obligation Tactic := idtac.

  Program Fixpoint bset {num ones d c} (B : tree w num ones d c) i
    {measure (size_of_tree B)} :
    { B'b : tree w num (ones + (~~ (daccess B i)) && (i < num)) d c * bool
    | dflatten (fst B'b) = bit_set (dflatten B) i/\snd B'b = ~~ daccess B i } :=
    match B with
    | Leaf s _ _ => (Leaf _ (bit_set s i) _ _, ~~ (access s i))
    | Node lnum lones rnum rones _ _ _ _ col cor l r =>
      match lt_dec i lnum with
      | left H =>
        let x := bset l i
        in (Node col cor x.1 r, x.2)
      | right H =>
        let x := bset r (i - lnum)
        in (Node col cor l x.1, x.2)
      end
    end.

  Next Obligation. intros. by rewrite size_bit_set. Qed.

  Next Obligation. intros. by rewrite size_bit_set. Qed.

  Next Obligation. intros; apply: size_bit_set. Qed.

  Next Obligation.
    intros; case Hi: (i < size s).
    rewrite /count_one /daccess (count_bit_set false). by rewrite andbT addnC.
    by rewrite Hi.
    rewrite andbF addn0. by rewrite /count_one /daccess bit_set_over //= leqNgt Hi.
  Qed.

  Next Obligation.
    intros; subst; split => //.
    by destruct bset_func_obligation_4 , bset_func_obligation_3 => /=.
  Qed.

  Next Obligation.
    intros; subst. apply /ltP.
    rewrite -Heq_B /=.
    by rewrite -addn1 leq_add2l size_of_tree_pos.
  Qed.

  Next Obligation.
    intros; move/ltP: (H) => Hi /=.
    by rewrite Hi (ltn_addr _ Hi) addnAC.
  Qed.

  Next Obligation.
    split; subst; last first.
      destruct bset as [[l' flip][Hl' Hf]] => /=.
      move/ltP: (H) => ->.
      by rewrite -Hf.
    move=> /=.
    move: (lones + rones + _) (bset_func_obligation_7 _ _ _ _ _ _) => ones Ho.
    destruct Ho => /=.
    destruct bset as [[l' flip][Hl' Hf]] => /=.
    rewrite /= in Hl'.
    move/ltP: (H).
    rewrite Hl' /bit_set update_cat {1}(size_dflatten l) => Hi.
    by rewrite ifT.
  Qed.

  Next Obligation.
    intros; subst. apply /ltP.
    rewrite -Heq_B /=.
    by rewrite -add1n leq_add2r size_of_tree_pos.
  Qed.

  Next Obligation.
    intros; move/ltP: (H) => Hi /=.
    rewrite -if_neg Hi !addnA.
    by rewrite -(ltn_add2l lnum) subnKC // leqNgt.
  Qed.

  Next Obligation.
    split; subst; last first.
      destruct bset as [[r' flip][Hr' Hf]] => /=.
      move/ltP: (H) => Hi.
      by rewrite -if_neg Hi -Hf.
    move=> /=.
    move: (lones + rones + _) (bset_func_obligation_10 _ _ _ _ _ _) => ones Ho.
    destruct Ho => /=.
    destruct bset as [[r' flip][Hr' Hf]] => /=.
    rewrite /= in Hr'.
    move/ltP: (H).
    rewrite Hr' /bit_set update_cat (size_dflatten l) => Hi.
    by rewrite -if_neg Hi.
  Qed.

  Next Obligation. intuition. Qed.

End set_clear.

Section delete.

  Lemma count_delete {arr i} : count_one arr - nth false arr i = count_one (delete arr i).
  Proof.
    case_eq (i < (size arr)) => H.
     rewrite -(cat_take_drop i arr) /delete /count_one !count_cat cat_take_drop (drop_nth false) // -/(cat [:: nth false arr i] _) count_cat /= addn0.
     case: (nth false arr i) => /=.
      by rewrite [1 + _]addnC addnA addn1 subn1 -[_.+1]subn0 subSKn subn0.
     by rewrite add0n subn0.
    rewrite ltnNge in H.
    move/negPn : H => H.
    rewrite nth_default /count_one /delete // take_oversize // drop_oversize.
     by rewrite count_cat /= addn0 subn0.
    by apply: leqW.
  Qed.

  Lemma delete_oversize {arr : seq bool} {i} : size arr <= i -> arr = delete arr i.
  Proof.
    move => H.
    rewrite /= /delete take_oversize // drop_oversize.
     by rewrite cats0.
     by apply: leqW.
  Qed.

  Lemma daccess_default {n m d c} (tr : tree w n m d c) : forall(i : nat), n <= i -> (daccess tr i) = false.
  Proof.
    elim: tr => /=. intros; by rewrite nth_default //.
    intros.
    case: ifP => H2.
     move: (ltn_addr s2 H2) => H3.
     move: (leq_ltn_trans H1 H3).
     by rewrite ltnn.
    move: (leq_sub2r s1 H1).
    rewrite addKn => H3.
    by apply: (H0 (i1 - s1) H3).
  Qed.

  (* NB: move? *)
  Lemma sizeW (arr : seq bool) : w ^ 2 %/ 2 <= size arr -> 0 < size arr.
  Proof.
    move/eqP: (wordsize_sqrn_div2_neq0 _ wordsize_gt1).
    rewrite -lt0n => ltn1.
    rewrite leq_eqVlt.
    case/orP => eq2. move/eqP: eq2 => eq2. by rewrite eq2 in ltn1.
    exact: (ltn_trans ltn1 eq2).
  Qed.

  Lemma delete_cat {arr arr' : seq bool} {i} : delete (arr ++ arr') i = (if i < size arr then delete arr i ++ arr' else arr ++ delete arr' (i - (size arr))).
  Proof.
    rewrite /delete take_cat -catA.
    case: ifP => H.
     rewrite drop_cat.
     case: ifP => // H2.
     move: (negbT H2).
     rewrite -leqNgt => H3.
     have H4 : i.+1 = size arr. apply/eqP. rewrite eqn_leq. by apply/andP.
     by rewrite H4 subnn drop0 drop_oversize //.
    rewrite drop_cat.
    case: ifP => H2. move: (ltnW H2). by rewrite H.
    move: (negbT H) (negbT H2).
    rewrite -!leqNgt => H3 H4.
    by rewrite catA subSn //.
  Qed.

  Lemma addnBAC a b c : a >= c -> (a + b) - c = (a - c) + b.
  Proof. by move => ?; rewrite addnC -addnBA // addnC. Qed.

  Lemma cons_head_behead (arr: seq bool) : (size arr) > 0 -> (access arr 0) :: (behead arr) = arr.
  Proof. case: arr => /= //. Qed.

  Lemma cat_head_behead (arr arr' : seq bool) : 0 < size arr' -> (rcons arr (access arr' 0)) ++ (delete arr' 0) = arr ++ arr'.
  Proof. move => H. rewrite !cat_rcons -!cat_cons take0 drop1 /= cons_head_behead //. Qed.

  Lemma cat_last_belast (arr arr' : seq bool) : 0 < size arr -> (delete arr (size arr).-1) ++ ((access arr (size arr).-1) :: arr') = arr ++ arr'.
  Proof.
    move => H.
    rewrite /delete /access drop_oversize;last by rewrite prednK.
    rewrite cats0.
    move: H.
    elim arr => // /= b arr'' IH.
    case H : (0 < size arr'').
     by rewrite -(IH H); destruct arr''.
    move/negP/negP in H.
    rewrite leqNgt in H.
    move/negPn in H.
    move: H.
    case arr'' => //.
  Qed.

  Lemma cons_delete {i} (arr arr' : seq bool) : 0 < size arr' ->
                                                (rcons (delete arr i) (access arr' 0)) ++ (delete arr' 0) = (delete arr i) ++ arr'.
  Proof. move => H. rewrite !cat_rcons -!catA -cat_cons take0 drop1 /= cons_head_behead //. Qed.

  Lemma size_rcons_delete {arr : seq bool} (i : nat) (b : bool) : i < size arr -> size (rcons (delete arr i) b) = size arr.
  Proof.
    move => G.
    rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
    case_eq i => [H|i' H]. by rewrite H in G.
    rewrite H in G.
    exact: (ltn_trans (ltn0Sn i') G).
  Qed.

  Lemma size_delete1 {arr : seq bool} (i : nat) : size arr = (size (delete arr i)) + (i < size arr).
  Proof.
    case_eq (i < size arr).
     move/idP => G.
     rewrite size_delete // -subn1 /= subnK //.
     case_eq i => [H|i' H]. by rewrite H in G.
     rewrite H in G.
     exact: (ltn_trans (ltn0Sn i') G).
    move/negP/negP => G.
    rewrite -leqNgt in G.
    rewrite /delete take_oversize // drop_oversize // /=;last first. exact: (leqW G).
    by rewrite cats0 addn0.
  Qed.

  Lemma leq_nth_count {i arr} : nth false arr i <= count_one arr.
  Proof.
    rewrite -(cat_take_drop i arr) /count_one count_cat nth_cat size_take.
    case: ifP. case: ifP => H. by rewrite ltnn. by rewrite H.
    case: ifP.
     rewrite subnn nth0 /head /(count_mem _).
     case (drop i arr) => // b.
     destruct b => //.
     case (take i arr) => // b.
     destruct b => // /= l r.
     rewrite add0n addnA ltn_addr // ltn_addl //.
    move/negP/negP => H ?.
    rewrite -leqNgt in H.
    rewrite nth_default;last first. rewrite size_drop. move/eqP: H => H. by rewrite H leq0n.
    by rewrite /= leq0n.
  Qed.

Lemma leq_divn2n_mul2 (a : nat) : a > 0 -> a %/ 2 + a %/ 2 < 2 * a.
Proof.
by move=> ?; rewrite mul2n divn2 addnn ltn_double -{1}(add0n a) avg_ltn_l.
Qed.

  Lemma ltn_subln a b c : c > 0 -> a < b + c = (a - b < c).
  Proof.
    case H1 : (b <= a) => H2. by rewrite -[RHS](ltn_add2r b) subnK // addnC.
    move: H1; rewrite leqNgt; move/negP/negP => H1.
    rewrite ltn_addr //. move: H1.
    case: b => // n H1.
    move/eqP: (ltnW H1) => W.
    by rewrite W H2.
  Qed.

  Lemma ltn_subrn a b c : b > 0 -> a < b + c = (a - c < b).
  Proof. rewrite addnC. exact: (ltn_subln a c b). Qed.

  Lemma sizeW' {s o d c} (tr : tree w s o d c) : s > 0.
  Proof. elim tr; intros; first apply sizeW => //; rewrite ltn_addr //. Qed.

  Inductive near_tree' : nat -> nat -> nat -> color -> Type :=
  | Stay : forall {s o d c} p,
      color_ok c (inv p) ->
      tree w s o d c -> near_tree' s o d p
  | Down : forall {s o d},
      tree w s o d Black -> near_tree' s o d.+1 Black.

  Definition dflatteni' {s o d c} (tr : near_tree' s o d c) :=
    match tr with
    | Stay _ _ _ _ _ _ t => dflatten t
    | Down _ _ _ t =>  dflatten t
   end.

  Definition black_of_red {s o d} (B : tree w s o d Red) : { B' : tree w s o (incr_black d Black) Black | dflatten B' = dflatten B }.

    move: B; move ceq : (Red) => c' B.
    move: B ceq => [//|? ? ? ? ? cl cr c ? ? l r] /= <-.
    by exists (bnode l r).
  Defined.

  Lemma leq_access_count {s o d c} : forall(B : tree w s o d c), forall(i : nat) , i < s -> daccess B i <= o.
  Proof.
    move => B.
    elim B => /=. intros. exact: leq_nth_count.
    move => s1 o1 s2 o2 d' cl cr c' ? ? l IHl r IHr.
    move => i H.
    case: ifP => H'.
    by rewrite (leq_trans (IHl _ H')) // leq_addr.
    rewrite (leq_trans _ (leq_addl _ _)) //.
    move: (IHr (i - s1)).
    rewrite -(ltn_add2r s1) subnK ;last by rewrite leqNgt H' /=.
    rewrite addnC => H''.
    exact: (H'' H).
  Qed.

  Definition merge_arrays (a b : seq bool) (i : nat) (w1 : w ^ 2 %/ 2 == size a) (w2 : w ^ 2 %/ 2 == size b) (val : i < size a + size b) :
             {tr : tree w (size a + size b - (i < size a + size b)) (count_one a + count_one b - (access (a ++ b) i)) 0 Black | dflatten tr = delete (a ++ b) i}.

    move/eqP : (wordsize_sqrn_div2_neq0 _ wordsize_gt1); rewrite -lt0n => pos.
    move/eqP: w1 => w1. move/eqP: w2 => w2. move: (pos); rewrite w1 => w1p. move: (pos); rewrite w2 => w2p.
    case Hl : (i < size a).
     have ueq : size ((rcons (delete a i) (access b 0)) ++ (delete b 0)) < 2 * w ^ 2.
      rewrite size_cat size_rcons !size_delete // prednK // -subn1 addnBA // subn1 -w1 -w2 ltnW // prednK //;last rewrite ltn_addl //.
      rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
     have leq : size (rcons (delete a i) (access b 0) ++ delete b 0) >= w ^ 2 %/ 2.
       by rewrite size_cat size_rcons !size_delete // prednK // w1 leq_addr.
     rewrite ltn_addr // addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat delete_cat addnBAC /access nth_cat Hl; last rewrite leq_nth_count //.
     rewrite count_delete -count_cat -cat_head_behead //.
     by exists (Leaf _ ((rcons (delete a i) (access b 0)) ++ (delete b 0)) leq ueq).
    move: val; rewrite ltn_subln // => Hr.
    have ueq : size (a ++ (delete b (i - (size a)))) < 2 * w ^ 2.
     rewrite size_cat size_delete // -w1 -w2 -subn1 addnBA // subn1 ltnW // prednK //;last rewrite ltn_addl //.
     rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
    have leq : size (a ++ (delete b (i - (size a)))) >= w ^ 2 %/ 2.
    rewrite size_cat size_delete //;last rewrite -{1}w1 w2 //.
      by rewrite leq_addr.
    rewrite Hr -addnBA // subn1 -(size_delete Hr) -size_cat -addnBA /access nth_cat Hl ;last rewrite leq_nth_count //.
      rewrite count_delete -count_cat.
    exists (Leaf _ (a ++ (delete b (i - (size a)))) leq ueq).
    by rewrite /= delete_cat Hl.
  Qed.

  Lemma xir_ok {c} : color_ok c (inv Red).
  Proof. move: c => [] //. Qed.

  Definition delete_from_leaves {s1 o1 s2 o2} p (l : tree w s1 o1 0 Black) (r : tree w s2 o2 0 Black) (i : nat) :
    {B' : near_tree' (s1 + s2 - (i < s1 + s2))
                    (o1 + o2 - access (dflatten l ++ dflatten r) i) (incr_black 0 p) p | dflatteni' B' = delete (dflatten l ++ dflatten r) i}.

    move/eqP : (wordsize_sqrn_div2_neq0 _ wordsize_gt1) (sizeW' l) (sizeW' r); rewrite -lt0n => pos posl posr.
    remember_eq 0 d' deq; remember_eq Black c' ceq; move: l r; rewrite -ceq -deq => l; destruct l as [al leql ueql|]; last rewrite ceq /= // in deq.
    move => {deq ceq}; remember_eq 0 d' deq; remember_eq Black c' ceq; rewrite /= -ceq -deq => r; destruct r as [ar leqr ueqr|]; last rewrite ceq /= // in deq.

    rewrite /access nth_cat.
    case: ifP => Hl.
     case bcl : (w ^ 2 %/ 2 == size al).
      case bcr : (w ^ 2 %/ 2 == size ar).
       case (merge_arrays al ar i bcl bcr (ltn_addr _ Hl)).
       rewrite /access nth_cat Hl => res resK.
       case: p;[ by exists (Stay Red xir_ok res) | by exists (Down res)].
      rewrite /=.
      rewrite leq_eqVlt bcr (size_delete1 0) posr /= addn1 in leqr,ueqr.
      rewrite -(size_rcons_delete i (access ar 0)) // in leql,ueql.
      rewrite addnC -addnBA // ltn_addl // subn1 -(size_delete Hl) addnC -size_cat addnBAC;last exact: leq_nth_count.
      rewrite count_delete -count_cat -cat_head_behead // count_cat size_cat.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf _ (rcons (delete al i) (access ar 0)) leql ueql) (Leaf _ (delete ar 0) leqr (ltnW ueqr))))
        | exists (Stay Black (black_any_ok Red) (bnode (Leaf _ (rcons (delete al i) (access ar 0)) leql ueql) (Leaf _ (delete ar 0) leqr (ltnW ueqr)))) ];
      by rewrite delete_cat Hl /= cat_head_behead.
     rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
     rewrite addnC -addnBA // ltn_addl // subn1 -(size_delete Hl) /= addnC addnBAC;last exact: leq_nth_count.
     rewrite count_delete.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf _ (delete al i) leql (ltnW ueql)) (Leaf _ ar leqr ueqr)))
        | exists (Stay Black (black_any_ok Red) (bnode (Leaf _ (delete al i) leql (ltnW ueql)) (Leaf _ ar leqr ueqr))) ];
     by rewrite delete_cat Hl.
    case Hrl : (i < size al + size ar).
     case bcr : (w ^ 2 %/ 2 == size ar).
      case bcl : (w ^ 2 %/ 2 == size al).
       rewrite -Hrl.
       case (merge_arrays al ar i bcl bcr Hrl).
       rewrite /access nth_cat Hl => res resK.
       case: p;[ by exists (Stay Red xir_ok res) | by exists (Down res)].
      rewrite leq_eqVlt bcl (size_delete1 (size al).-1) prednK //= leqnn addn1 in leql,ueql.
      move/eqP/eqP in bcl. move/eqP in bcr.
      have leqr' : w ^ 2 %/ 2 <= size ((access al (size al).-1) :: (delete ar (i - size al))).
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
      have ueqr' : size ((access al (size al).-1) :: (delete ar (i - size al))) < 2 * w ^ 2.
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
     rewrite -!addnBA //;last by apply leq_nth_count.
     rewrite count_delete -count_cat /= subn1 [size ar](size_delete1 (i - size al)) -ltn_subln // Hrl -subn1 -addnBA // subnn addn0 -size_cat -cat_last_belast // size_cat count_cat.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf _ (delete al (size al).-1) leql (ltnW ueql)) (Leaf _ ((access al (size al).-1) :: (delete ar (i - size al))) leqr' ueqr')))
        | exists (Stay Black (black_any_ok Red) (bnode (Leaf _ (delete al (size al).-1) leql (ltnW ueql)) (Leaf _ ((access al (size al).-1) :: (delete ar (i - size al))) leqr' ueqr'))) ];
     by rewrite delete_cat Hl /= cat_last_belast.
    rewrite /=.
    rewrite leq_eqVlt bcr (size_delete1 (i - size al)) -ltn_subln // Hrl addn1 /= in leqr,ueqr.
    rewrite -!addnBA //;last exact: leq_nth_count.
    rewrite count_delete subn1 [size ar](size_delete1 (i - size al)).
    rewrite -ltn_subln // Hrl -subn1 -addnBA // subnn addn0.
    case: p;
      [ exists (Stay Red xir_ok (rnode (Leaf _ al leql ueql) (Leaf _ (delete ar (i - size al)) leqr (ltnW ueqr))))
      | exists (Stay Black (black_any_ok Red) (bnode (Leaf _ al leql ueql) (Leaf _ (delete ar (i - size al)) leqr (ltnW ueqr)))) ];
    by rewrite delete_cat Hl.
   rewrite /= nth_default;last rewrite ltn_subln // in Hrl;last by rewrite leqNgt Hrl.
   rewrite !subn0.
   case: p;
     [ exists (Stay Red xir_ok (rnode (Leaf _ al leql ueql) (Leaf _ ar leqr ueqr)))
     | exists (Stay Black (black_any_ok Red) (bnode (Leaf _ al leql ueql) (Leaf _ ar leqr ueqr))) ];
   by rewrite -delete_oversize // size_cat leqNgt Hrl.
  Defined.

  Definition balright {s1 s2 o1 o2 d cl cr} (p : color)
             (l : tree w s1 o1 d cl)
             (dr : near_tree' s2 o2 d cr) :
    color_ok p cl ->
    color_ok p cr ->
  {B' : near_tree' (s1 + s2) (o1 + o2) (incr_black d p) p |
  dflatteni' B' = dflatten l ++ dflatteni' dr}.

    move: p => [].
     move: cl cr l dr => [] [] // l dr ? ?.
     move: l dr; move ceq : (Black) => c' l dr.
     move: dr ceq l => /= [? ? d' c p ok dr|? ? d' dr] ceq l.
      move: ceq c ok l dr => <- [] // ? l dr.
      by exists (Stay Red xir_ok (rnode l dr)).
     move: l dr => {ceq c'} /=; move ceq : (Black) => c'; move deq : (d'.+1) => d'' l dr.
     move: l deq ceq dr => [//| ? ? ? ? ? ? clr c cllok clrok ll lr] deq ceq dr.
     move: ceq deq ll lr dr cllok clrok => <- /= [] <- ll lr dr clrok ?.
     move: clr lr clrok => [] lr ? {c'}.
      move: ll lr dr; move ceq : (Red) => c' ll lr dr.
      move: lr ll dr ceq => [//| ? ? ? ? ? cl' cr' cll okl okr lrl lrr] ll dr ceq.
      move: ceq cl' cr' okl okr ll lrl lrr dr => /= <- [] [] //= ? ? ll lrl lrr dr.
      rewrite !addnA -![_ + _ + _ + _]addnA.
      exists (Stay Red xir_ok (rnode (bnode ll lrl) (bnode lrr dr))).
      by rewrite /= !catA.
     rewrite -!addnA -catA.
     by exists (Stay Red xir_ok (bnode ll (rnode lr dr))).
    move => /= ? ?.
    move: dr l => [? ? d' c ? ? dr|? ? d' dr] l; first by exists (Stay Black (black_any_ok Red) (bnode l dr)).
    move: dr l => /=; move deq : (d'.+1) => d'' dr l.
    move: l deq dr => [//| ? oo ? ? ? cll clr c cllok clrok ll lr] /=.
    move: clr clrok lr => [] clrok lr.
     move: c cllok clrok => [] //= ? ? [] -> dr.
     move: lr; move ceq : (Red) => c' lr.
     move: lr ceq dr ll => /= [//|? ? ? ? ? cl' cr' ? okl okr lrl lrr] ceq dr ll.
     move: ceq cl' cr' ll lrl lrr okl okr dr => <- [] [] //= ll lrl lrr ? ? dr.
     rewrite !addnA -![_ + _ + _ + _]addnA.
     exists (Stay Black (black_any_ok Red) (bnode (bnode ll lrl) (bnode lrr dr))).
     by rewrite /= -!catA.
    move: c cllok clrok => [] /= cllok clrok.
     move: cll cllok ll => [] // ? ll deq.
     move: lr ll ; move ceq : (Black) => c' lr ll dr.
     move: lr ceq deq ll dr => [//| ? ? ? ? ? cl' cr' crl okl okr lrl lrr] ceq deq ll dr.
     move: ceq deq lrl lrr ll dr okl okr => /= <- [] <- lrl lrr ll dr /= ? ?.
     move: cr' lrr  => [] lrr;last first.
      rewrite -!addnA.
      exists (Stay Black (black_any_ok Red) (bnode ll (bnode lrl (rnode lrr dr)))).
      by rewrite /= -!catA.
     move: lrr => /=; move ceq : (Red) => c lrr {c'}.
     move: lrr ceq lrl ll dr => [//| ? ? ? ? ? clrrl clrr c' okl okr lrrl lrrr] ceq lrl ll dr.
     move: ceq clrrl clrr lrrl lrrr lrl ll dr okl okr => <- [] [] // lrrl lrrr lrl ll dr ? ?.
     rewrite -!addnA [X in (_ + X)]addnA [X in (oo + X)]addnA.
     exists (Stay Black (black_any_ok Red) (bnode ll (rnode (bnode lrl lrrl) (bnode lrrr dr)))).
     by rewrite /= -!catA.
    move => [] -> dr.
    rewrite -!addnA -!catA.
    by exists (Down (bnode ll (rnode lr dr))).
  Defined.

  Definition balleft {s1 s2 o1 o2 d cl cr} (p : color)
             (dl : near_tree' s1 o1 d cl)
             (r : tree w s2 o2 d cr) :
    color_ok p cl ->
    color_ok p cr ->
  {B' : near_tree' (s1 + s2) (o1 + o2) (incr_black d p) p |
  dflatteni' B' = dflatteni' dl ++ dflatten r}.

    move: p => [].
     move: cl cr dl r => [] [] // dl r ? ?.
     move: dl r; move ceq : (Black) => c' dl r.
     move: dl ceq r => /= [? ? d' c p ok dl|? ? d' dl] ceq r.
      move: ceq c ok r dl => <- [] // ? r dl.
      by exists (Stay Red xir_ok (rnode dl r)).
     move: dl r => {ceq c'} /=; move ceq : (Black) => c'; move deq : (d'.+1) => d'' dl r.
     move: r deq ceq dl => [//| ? ? ? ? ? crl ? c crlok crrok rl rr] deq ceq dl.
     move: ceq deq rl rr dl crlok crrok => <- /= [] <- rl rr dl crlok ?.
     move: crl rl crlok => [] rl ? {c'}.
      move: rl rr dl; move ceq : (Red) => c' rl rr dl.
      move: rl rr dl ceq => [//| ? ? ? ? ? cl' cr' crl okl okr rll rlr] rr dl ceq.
      move: ceq cl' cr' okl okr rr rll rlr dl => /= <- [] [] //= ? ? rr rll rlr dl.
      rewrite !addnA -![_ + _ + _ + _]addnA.
      exists (Stay Red xir_ok (rnode (bnode dl rll) (bnode rlr rr))).
      by rewrite /= !catA.
     rewrite !addnA /= !catA.
     by exists (Stay Red xir_ok (bnode (rnode dl rl) rr)).
    move => /= ? ?.
    move: dl r => [? ? d' c ? ? dl|? ? d' dl] r; first by exists (Stay Black (black_any_ok Red) (bnode dl r)).
    move: dl r => /=; move deq : (d'.+1) => d'' dl r.
    move: r deq dl => [//| ? ? ? ? ? crl crr c crlok crrok rl rr] /=.
    move: crl crlok rl => [] crlok rl.
     move: c crlok crrok => [] //= ? ? [] -> dl.
     move: rl; move ceq : (Red) => c' rl.
     move: rl ceq dl rr => /= [//|? ? ? ? ? cl' cr' crl okl okr rll rlr] ceq dl rr.
     move: ceq cl' cr' rr rll rlr okl okr dl => <- [] [] //= rr rll rlr ? ? dl.
     rewrite !addnA -![_ + _ + _ + _]addnA.
     exists (Stay Black (black_any_ok Red) (bnode (bnode dl rll) (bnode rlr rr))).
     by rewrite /= -!catA.
    move: c crrok crlok => [] /= crrok crlok.
     move: crr crrok rr => [] // ? rr deq.
     move: rl rr; move ceq : (Black) => c' rl rr dl.
     move: rl ceq deq rr dl => [//| ? ? ? ? ? cl' cr' crl okl okr rll rlr] ceq deq rr dl.
     move: ceq deq rll rlr rr dl okl okr => /= <- [] <- rll rlr rr dl /= ? ?.
     move: cl' rll  => [] rll;last first.
      rewrite !addnA.
      exists (Stay Black (black_any_ok Red) (bnode (bnode (rnode dl rll) rlr) rr)).
      by rewrite /= -!catA.
     move: rll; move ceq : (Red) => c rll {c'}.
     move: rll ceq rlr rr dl=> [//| ? ? ? o3 ? crll crlr c' okl okr rlll rllr] ceq rlr rr dl.
     move: ceq crll crlr rlll rllr rlr rr dl okl okr => <- [] [] // rlll rllr rlr rr dl ? ?.
     rewrite -!addnA ![_ + ( _ + (_ + (_ + _)))]addnA [X in _ + _ + X]addnA [o3 + (_ + _)]addnA.
     exists (Stay Black (black_any_ok Red) (bnode (bnode dl rlll) (rnode (bnode rllr rlr) rr))).
     by rewrite /= -!catA.
    move => [] -> dl.
    rewrite !addnA !catA.
    by exists (Down (bnode (rnode dl rl) rr)).
  Defined.

  Lemma access_cat s t i : access (s ++ t) i = (if i < size s then access s i else access t (i - size s)).
  Proof. by rewrite /access nth_cat. Qed.

  Lemma cic_ok {c} : color_ok c (inv c).
  Proof. by destruct c. Qed.

  Lemma ltn_subLN a b c : 0 < c -> (a < b + c) -> (a - b < c).
  Proof. move => H H'. rewrite -ltn_subln //. Qed.

  Lemma ltn_subLN2 a b c i : 0 < c ->
                             i < a + b + c ->
                             (i < a + b) = false ->
                             i - a - b < c.
  Proof.
    move => H H'; rewrite ltnNge.
    move/negPn => H''.
    rewrite -!ltn_subln //;
     first by rewrite addnA.
    by apply: ltn_addl.
  Qed.

Lemma leq_addln a b c : a <= b -> a <= b + c.
Proof. by move/leq_trans; apply; rewrite leq_addr. Qed.

Lemma leq_addrn a b c : a <= c -> a <= b + c.
Proof. by move/leq_trans; apply; rewrite leq_addl. Qed.

Hint Resolve ltn_subLN ltn_subLN2 addnA leq_addr leq_addrn ltn_addl ltn_addr cic_ok leq_access_count sizeW'.

Lemma ordinal_caseL {s1 o1 s2 o2 d i cl cr} c
      (lok : color_ok c cl)
      (rok : color_ok c cr)
      (l : tree w s1 o1 d cl)
      (r : tree w s2 o2 d cr) :
      i < s1 -> 
      {B' : near_tree' (s1 - 1) (o1 - daccess l i) d cl | dflatteni' B' = delete (dflatten l) i} ->
      {B' : near_tree' (s1 + s2 - 1) (o1 + o2 - daccess l i) (incr_black d c) c | dflatteni' B' = delete (dflatten l) i ++ dflatten r }.
Proof.
  move=> H dl.
  rewrite !addnBAC; eauto.
  apply: exist; apply: etrans;
  first by (apply (proj2_sig (balleft c (proj1_sig dl) r lok rok))).
  congr (_ ++ _); by apply: (proj2_sig dl).
Qed.

Lemma ordinal_caseR {s1 o1 s2 o2 d i cl cr} c
      (lok : color_ok c cl)
      (rok : color_ok c cr)
      (l : tree w s1 o1 d cl)
      (r : tree w s2 o2 d cr) :
      i < s1 + s2 -> 
      {B' : near_tree' (s2 - 1) (o2 - daccess r (i - s1)) d cr | dflatteni' B' = delete (dflatten r) (i - s1)} ->
      {B' : near_tree' (s1 + s2 - 1) (o1 + o2 - daccess r (i - s1)) (incr_black d c) c | dflatteni' B' = dflatten l ++ delete (dflatten r) (i - s1)}.
Proof.
  move=> H dr.
  rewrite -!addnBA; eauto.
  apply: exist; apply: etrans;
  first (apply: (proj2_sig (balright c l (proj1_sig dr) lok rok));
         apply: ltn_subLN; by eauto);
  congr (_ ++ _); by apply: (proj2_sig dr).
Qed.

Definition ddelete (d: nat) (c: color) (num ones : nat) (i : nat) (B : tree w num ones (incr_black d c) c) :
    { B' : near_tree' (num - (i < num)) (ones - (daccess B i)) (incr_black d c) c | dflatteni' B' = delete (dflatten B) i }.
  case val : (i < num);last first.
   move/negP/negP : val;
   rewrite ltnNge; move/negPn => val;
   rewrite daccess_default // !subn0 -delete_oversize;
   last by rewrite size_dflatten.
   apply: (exist _ (Stay _ _ B)) => //.

  move: B; move dceq: (incr_black d c) => d' B;
  elim: B d dceq i val => {c} // [s1 o1 ? ? d'' [] [] c // g1 g2 l IHl r IHr] d dceq i val;
  (have dceq' : d = d'' by case: c dceq g1 g2 => //=; case => //);
  move: dceq' l r IHl IHr => /= <- l r IHl IHr {dceq};
  rewrite delete_cat size_dflatten;
  case: ifP => H;
  (* most general cases *)
  try (apply: (ordinal_caseL c _ _ l r H (IHl d erefl i H)); by eauto);
  try (apply: (ordinal_caseR c _ _ l r val (IHr d erefl (i - s1) _));
       eauto; apply: ltn_subLN; by eauto).

  case: d r l IHl IHr val H => {d' d''} [| d r l _ IHr val H] /=.
   move creq: Red => cr;
   move cbeq: Black => cb; move deq: 0 => d r l.
   case: l creq cbeq deq r => // ? ? ? ? ? [] [] [] // ? ? ll lr ? <- /= deq r _ _ val H.
   move: deq ll lr r val H => <- ll lr r val H.
   move: (delete_from_leaves Red lr r (i - (size (dflatten ll)))).
   rewrite delete_cat access_cat -!daccessK !size_dflatten -!ltn_subln ; eauto.
   rewrite H !addnA val subnDA /= -!addnA -!addnBA; eauto => dr.
   apply: exist; apply: etrans.
   apply: (proj2_sig (balright c ll (proj1_sig dr) _ _)); eauto.
   rewrite -!catA; congr (_ ++ _).
   apply: (proj2_sig dr).
  apply: (ordinal_caseR c _ _ l r val (IHr d erefl (i - s1) _));
   eauto; apply: ltn_subLN; by eauto.
  
  case: d r l IHl IHr val H => {d' d''} [| d r l IHl _ val H] /=.
   move creq: Red => cr;
   move cbeq: Black => cb'; move deq: 0 => d r l.
   case: r creq cbeq deq l => // ? ? ? ? ? [] [] [] // ? ? rl rr ? <- /= deq l _ _ val H.
   move: deq rl rr l val H => <- rl rr l val H.
   move: (delete_from_leaves Red l rl i).
   rewrite delete_cat access_cat -!daccessK !size_dflatten; eauto.
   rewrite ltn_addr H /=; auto => dl.
   rewrite !addnA.
   rewrite [s1 + _ + _ - _]addnBAC; eauto.
   rewrite [o1 + _ + _ - _]addnBAC; eauto.
   apply: exist; apply: etrans.
   apply: (proj2_sig (balleft c (proj1_sig dl) rr _ _ )); eauto.
   rewrite !catA; congr (_ ++ _).
   exact: (proj2_sig dl).
   by rewrite (leq_trans _ (leq_addr _ _)) // leq_access_count.
  apply: (ordinal_caseL c _ _ l r H (IHl d erefl i H)); by eauto.

  case: d l r IHl IHr => [l r _ _| d l r IHl _].
   move: (delete_from_leaves c l r i).
   by rewrite access_cat delete_cat size_dflatten H val /= daccessK.
  apply: (ordinal_caseL c _ _ l r H (IHl d erefl i H)); by eauto.

  case: d l r IHl IHr => [l r _ _| d l r _ IHr].
   move: (delete_from_leaves c l r i).
   by rewrite access_cat delete_cat size_dflatten H val /= daccessK.
  apply: (ordinal_caseR c _ _ l r val (IHr d erefl (i - s1) _));
   eauto; apply: ltn_subLN; by eauto.
Qed.
End delete.

End dynamic_dependent.
Extract Inductive tree => tree_ml [ "LeafML" "(function (s1,o1,s2,o2,d,c,cl,cr,l,r) -> NodeML (s1, o1, s2, o2, c, l, r))" ]
"(fun fl fn ->
  function
  | LeafML arr -> fl arr
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 1 cl cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 1 Black cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 1 Black Black c l r
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 1 cl Black c l r)".
Extraction TestCompile dinsert ddelete tree_ml.
Extraction "dydep.ml" dinsert ddelete tree_ml.
