From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program JMeq set_clear.

Set Implicit Arguments.

Variable w : nat.
Axiom wordsize_pos: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. apply ltnW. exact wordsize_pos. Qed.

Lemma wordsize_neq0: w != 0.
Proof. rewrite -lt0n. exact wordsize_gt0. Qed.

Section insert.
  Inductive color := Red | Black.

  Definition color_ok parent child : bool :=
    match parent,child with
    | Red,Red => false
    | _,_ => true
    end.

  Definition incr_black d c :=
    match c with
    | Black => d.+1
    | _ => d
    end.

  Definition is_black c :=
    match c with
    | Black => true
    | _ => false
    end.

  Lemma incr_black_prop d c : incr_black d c = d + is_black c.
  Proof. case: c => //=. by rewrite addn1. Qed.

  Definition inv c :=
    match c with
    | Black => Red
    | Red => Black
    end.

  Inductive param (A : Type) : Prop := Param : A -> param A.

  Definition inc_black d c :=
    match c, d with
    | Black, Param n => Param n.+1
    | _, _ => d
    end.

  Definition app_param (A B : Type) (f : A -> B) (x : param A) :=
    let: Param x := x in Param (f x).

  (* work around for program fixpoint *)
  Definition count_one arr := count_mem true arr.

  Inductive tree : nat -> nat -> param nat -> color -> Type :=
  | Leaf : forall (arr : seq bool),
      (w ^ 2) %/ 2 <= (size arr) ->
      2 * (w ^ 2) > (size arr) ->
      tree (size arr) (count_one arr) (Param 0) Black
  | Node : forall {s1 o1 s2 o2 d cl cr c},
      color_ok c cl -> color_ok c cr ->
      tree s1 o1 d cl -> tree s2 o2 d cr ->
      tree (s1 + s2) (o1 + o2) (inc_black d c) c.

  Fixpoint size_of_tree {s o d c} (t : tree s o d c) : nat :=
    match t with
    | Leaf _ _ s => 1
    | Node _ _ _ _ _ _ _ _ _ _ l r => size_of_tree l + size_of_tree r
    end.

  Lemma size_of_tree_pos num ones d c (B : tree num ones d c) :
    size_of_tree B > 0.
  Proof.
    elim: B => //= lnum lones rnum rones d' cl cr c' ok_l ok_r l IHl r IHr.
    by rewrite addn_gt0 IHl orTb.
  Qed.

  Definition rb_ok: color_ok Red Black := erefl.

  Definition bx_ok x : color_ok Black x := erefl.

  Definition rnode {s1 s2 o1 o2 d} (l : tree s1 o1 d Black)
             (r : tree s2 o2 d Black) : tree (s1 + s2) (o1 + o2) d Red :=
    Node rb_ok rb_ok l r.

  Definition bnode {s1 s2 o1 o2 d cl cr} (l : tree s1 o1 d cl)
             (r : tree s2 o2 d cr)
           : tree (s1 + s2) (o1 + o2) (inc_black d Black) Black :=
    Node (bx_ok cl) (bx_ok cr) l r.

  Inductive near_tree : nat -> nat -> param nat -> color -> Type :=
  | Bad : forall {s1 o1 s2 o2 s3 o3 d},
      tree s1 o1 d Black ->
      tree s2 o2 d Black ->
      tree s3 o3 d Black ->
      near_tree (s1 + s2 + s3) (o1 + o2 + o3) d Red
  | Good: forall {s o d c} p,
      tree s o d c ->
      near_tree s o d p.

  (* Xuanrui: I see no point to define fix_color in Ltac...
   * Gallina would be much more readable here
   * Kazunari: I totally agree. sorry for being lazy. 
   *)
  
  Definition fix_color {nl ml d c} (l : near_tree nl ml d c) :=
    match l with
    | Bad _ _ _ _ _ _ _ _ _ _ => Red
    | Good _ _ _ _ _ _ => Black
    end.

  (* Xuanrui: same, programming those in Ltac makes little sense to me *)

  Definition black_of_bad {nl ml d c} (l : near_tree nl ml d c) :=
    match l with
    | Bad _ _ _ _ _ _ _ _ _ _ => Black
    | Good _ _ _ c _ _ => c
    end.

  Definition real_tree {nl ml d c} (t : near_tree nl ml d c) : tree nl ml (inc_black d (inv (fix_color t))) (black_of_bad t) :=
    match t with
    | Bad _ _ _ _ _ _ _ x y z => bnode (rnode x y) z
    | Good _ _ _ _ _ t' => t'
    end.
  
  Fixpoint dflatten {n m d c} (B : tree n m d c) :=
    match B with
    | Node _ _ _ _ _ _ _ _ _ _ l r => dflatten l ++ dflatten r
    | Leaf s _ _ => s
    end.

  Lemma dflatten_sizeK {n m d c} (B : tree n m d c) : size (dflatten B) = n.
  Proof.
    elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
    by rewrite size_cat IHl IHr.
  Qed.
  
  Definition dflattenn {n m d c} (B : near_tree n m d c) :=
    match B with
    | Bad _ _ _ _ _ _ _ x y z => dflatten x ++ dflatten y ++ dflatten z
    | Good _ _ _ _ _ t => dflatten t
    end.

  Definition balanceL {nl ml d cl cr nr mr} (p : color) (l : near_tree nl ml d cl) (r : tree nr mr d cr):
    color_ok p (fix_color l) -> (* important claim! *)
    color_ok p cr ->
    {tr : near_tree (nl + nr) (ml + mr) (inc_black d p) p | dflattenn tr = dflattenn l ++ dflatten r}.

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

  Definition balanceR {nl ml d cl cr nr mr} (p : color) (l : tree nl ml d cl) (r : near_tree nr mr d cr):
    color_ok p cl ->
    color_ok p (fix_color r) ->  (* important claim! *)
    {tr : near_tree (nl + nr) (ml + mr) (inc_black d p) p | dflattenn tr = dflatten l ++ dflattenn r}.

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

  Lemma dflatten_size num ones d c (B : tree num ones d c) :
    num = size (dflatten B).
  Proof.
    elim: B => //= s1 o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr.
    by rewrite size_cat -IHl -IHr.
  Qed.

  Program Fixpoint dinsert' {n m d c} (B : tree n m d c) (b : bool) i
          {measure (size_of_tree B)} : { B' : near_tree n.+1 (m + b) d c
                              | dflattenn B' = insert1 (dflatten B) b i } :=
    match B with
    | Leaf s _ _ =>
      let s' := insert1 s b i in
      match size s' == 2 * (w ^ 2) with
      | true => let n  := (size s') %/ 2 in
                let sl := take n s' in
                let sr := drop n s' in
                Good c (rnode (Leaf sl _ _) (Leaf sr _ _))
      | false => Good c (Leaf s' _ _)
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
    rewrite /dflattenn /insert1.
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
    rewrite /dflattenn /insert1.
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
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
    - set B' := balanceR _ _ _ _ _.
      rewrite /dflattenn /eq_rect => /=.
      destruct dinsert'_func_obligation_23, dinsert'_func_obligation_22, dinsert'_func_obligation_21.
      rewrite -/(dflattenn (proj1_sig B')) (proj2_sig B') {B'}.
      destruct dinsert' => /=.
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
  Qed.

  Definition dinsert n m d c (B : tree n m d c) (b : bool) (i : nat) :=
    real_tree (proj1_sig (dinsert' B b i)).

  Lemma real_treeK nl ol d c (t : near_tree nl ol d c) :
    dflatten (real_tree t) = dflattenn t.
  Proof. case: t => //= n1 o1 n2 o2 n3 o3 d' x y z. by rewrite catA. Qed.
  
  Lemma dinsertK n m d c (B : tree n m d c) b i :
    dflatten (dinsert B b i) = insert1 (dflatten B) b i.
  Proof. by rewrite /dinsert real_treeK (proj2_sig (dinsert' B b i)). Qed.
  
End insert.

Section query.
  
  Fixpoint daccess {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => nth false s i
    | Node lnum _ _ _ _ _ _ _ _ _ l r =>
      if i < lnum
      then daccess l i
      else daccess r (i - lnum)
    end.

  Fixpoint drank {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => rank true i s
    | Node lnum lones rnum rones _ _ _ _ _ _ l r =>
      if i < lnum
      then drank l i
      else lones + drank r (i - lnum)
    end.

  Fixpoint dselect_0 {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => select false i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      let zeroes := s1 - o1
      in if i <= zeroes 
      then dselect_0 l i
      else s1 + dselect_0 r (i - zeroes)
    end.

  Fixpoint dselect_1 {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => select true i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      if i <= o1
      then dselect_1 l i
      else s1 + dselect_1 r (i - o1)
    end.

  Definition access (s : seq bool) i := nth false s i.

  Lemma dflatten_ones num ones d c (B : tree num ones d c) :
    ones = count_mem true (dflatten B).
  Proof.
    elim: B => //= s1 o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr.
    by rewrite count_cat -IHl -IHr.
  Qed.

  Lemma predC_bool b : predC (pred1 b) =1 pred1 (negb b).
  Proof. by case. Qed.

  Lemma count_mem_false_true (s : seq bool) :
    count_mem false s + count_mem true s = size s.
  Proof.
    by rewrite -(count_predC (pred1 false)) (eq_count (predC_bool false)).
  Qed.

  Lemma ones_lt_num num ones d c (B : tree num ones d c) :
    ones <= num.
  Proof.
    by rewrite (dflatten_ones B) [in X in _ <= X](dflatten_size B) count_size.
  Qed.

  Lemma dflatten_zeroes num ones d c (B : tree num ones d c) :
    num - ones = count_mem false (dflatten B).
  Proof.
    rewrite [in LHS](dflatten_ones B) [in X in X - _](dflatten_size B).
    apply/eqP. rewrite -(eqn_add2r (count_mem true (dflatten B))) subnK.
      by rewrite count_mem_false_true.
    by rewrite -(dflatten_ones B) -(dflatten_size B)(ones_lt_num B).
  Qed.
    
  Lemma dflatten_rank num ones d c (B : tree num ones d c) :
    ones = rank true num (dflatten B).
  Proof.
    by rewrite /rank [X in take X _](dflatten_size B) take_size -dflatten_ones.
  Qed.
    
  Lemma daccessK nums ones d c (B : tree nums ones d c) :
    daccess B =1 access (dflatten B).
  Proof.
    rewrite /access.
    elim: B => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite nth_cat -dflatten_size -IHl -IHr.
  Qed.

  Lemma drankK nums ones d c (B : tree nums ones d c) i :
    drank B i = rank true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite rank_cat -dflatten_size IHl -IHr -dflatten_rank.
  Qed.

  Lemma drank_ones num ones d c (B : tree num ones d c) :
    drank B num = ones.
  Proof.
    by rewrite [in RHS](dflatten_rank B) drankK.
  Qed.

  Lemma dselect1K nums ones d c (B : tree nums ones d c) i :
    dselect_1 B i = select true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_ones IHl IHr -dflatten_size. 
  Qed.

  Lemma dselect0K nums ones d c (B : tree nums ones d c) i :
    dselect_0 B i = select false i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_zeroes IHl IHr -dflatten_size.
  Qed.
  
End query.

(* Section added by Xuanrui
 * because I wanted to experiment with this version as well...
 * 
 * Feel free to comment this out or remove this...
 *)
Require Import Compare_dec.

Section set_clear.
  Obligation Tactic := idtac.
  
  Program Fixpoint bset {num ones d c} (B : tree num ones d c) i
    {measure (size_of_tree B)} :
    { B'b : (tree num (ones + (~~ (daccess B i)) && (i < num)) d c * bool)
    | dflatten (fst B'b) = bit_set (dflatten B) i/\snd B'b = ~~ daccess B i } :=
    match B with
    | Leaf s _ _ => (Leaf (bit_set s i) _ _, ~~ (access s i))
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
      by rewrite /count_one /access (count_bit_set' false Hi) andbT.
    by rewrite andbF addn0 bit_set_over //= leqNgt Hi.
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
    rewrite Hl' /bit_set update_cat -{1}(dflatten_size l) => Hi.
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
    rewrite Hr' /bit_set update_cat -(dflatten_size l) => Hi.
    by rewrite -if_neg Hi.
  Qed.

  Next Obligation. intuition. Qed.
                   
End set_clear.

Section delete.

  Definition wordsize_ok {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => ((w ^ 2) %/ 2 < (size s)) && (2 * (w ^ 2) >= (size s))
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => true
    end.

  Definition is_node {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => false
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => true
    end.

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

  Lemma daccess_default {n m d c} (tr : tree n m d c) : forall(i : nat), n <= i -> (daccess tr i) = false.
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

  Lemma technical : forall(n : nat),n == n %/ 2 -> n == 0.
  Proof.
    move => n.
    move/eqP.
    rewrite {1}(divn_eq n 2) muln2 -addnn -[RHS]addn0 -addnA.
    move/eqP.
    rewrite eqn_add2l.
    case: n => // n.
    case: n => // n.
    rewrite -addn2 divnDr // divnn /= modnDr.
    by rewrite !addn_eq0 [1 == 0]gtn_eqF // andbF andFb.
  Qed.


  Lemma size_of_node {n m d c} (tr : tree n m d c) : is_node tr -> n >= w ^ 2.
  Proof.
    Admitted.
    (* elim: tr => //. *)
    (* intros. *)
    (* destruct t;last first. *)

  Lemma sizeW (arr : seq bool) : w ^ 2 %/ 2 <= size arr -> 0 < size arr.
  Proof.
    Admitted.
    (* rewrite lt0n. *)
    (* move/eqP => H. *)
    (* have H2 : size arr = 0 -> w ^ 2 < 2. *)
    (*  move => H2. rewrite H2 subn0 in H. *)
    (*  by rewrite (divn_eq (w ^ 2) 2) H mul0n add0n ltn_pmod //. *)
    (* move: (contra H2). *)
    (* move: (contra (w ^ 2 %/ 2 <= size arr -> ) (size arr != 0)). *)
    (* apply/eqP. *)
    (* move : H. *)

    (* have: size arr == 0. *)
    (* apply/eqP. *)
    (* case/orP: (leq_total 0 (size arr)) => //. *)
    (* have H : w ^ 2 > 0. by rewrite expn_gt0 wordsize_gt0. *)
    (* have: w ^ 2 %/ 2 > 0. *)
    (* rewrite divn_gt0. *)
    (* rewrite -{1}(div0n 2) ltn_divLR // divnK. *)
    (* done. *)

    (* rewrite leq_divRL. *)

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

  Lemma technical2 {d}: (match d with
                         | Param n => Param n.+1
                         end = Param 0) = false.
  Proof.
    Admitted.

    (* destruct d. *)
    (* Compute (Param 0 = Param 1). *)
    (* About app_param. *)

  Lemma technical3 : forall(a b c : nat),a >= c -> a + b - c = a - c + b.
  Proof.
    move => a b c.
    move: b a.
    elim: c => [|c IH b]. intros. by rewrite !subn0.
    move => a H.
    rewrite !subnS (IH b a (ltnW H)) -!subn1.
    elim: b => [|b IH2]. by rewrite !addn0.
    rewrite -addnBA // -addn1 -addnBA // subnn addn0 addnA -IH2.
    rewrite subn1 addn1 prednK // -(IH b a (ltnW H)).
    clear IH2.
    case: b => [|b]. by rewrite addn0 subn_gt0.
    apply/eqP.
    rewrite -[b.+1]addn1 addnA addn1 [(a + b).+1 - c]subSn.
     rewrite -addn1 subSS //.
    have H2 : a <= a + b. exact: leq_addr.
    exact: (leq_trans (ltnW H) H2).
  Qed.

  Lemma cons_head_behead (arr: seq bool) : (size arr) > 0 -> (access arr 0) :: (behead arr) = arr.
  Proof. case: arr => /= //. Qed.

  Fixpoint ddelete {num ones d c} (B : tree num ones d c) i (okB: wordsize_ok B) (oki : i < num) :
    { B' : near_tree (num - 1) (ones - (daccess B i)) d c | dflattenn B' = delete (dflatten B) i}.

    destruct B.
     rewrite subn1 -(size_delete oki) count_delete.
     case/andP: okB => w1 w2.
     have H : size arr = (size (delete arr i)).+1.
      rewrite (size_delete oki) -subn1 -addn1 subnK //.
      by apply: sizeW.
     rewrite H in w1,w2.
     by exists (Good Black (Leaf (delete arr i) w1 w2)).
    rewrite /daccess //= delete_cat dflatten_sizeK.
    case: ifP => H.
     case_eq (s1 == (w ^ 2) %/ 2) => H2.
     (* B1 = Leaf, B2 = Leaf or (Red Leaf Leaf)*)
     destruct B1;last first.
      move/implyP: (size_of_node (Node i2 i3 B1_1 B1_2)) => /=.
      move/eqP: H2 => H2.
      rewrite H2 => H3.
      move: (leq_div (w ^ 2) 2) => H4.
      have H5 : w ^ 2 == w ^ 2 %/ 2. rewrite eqn_leq. apply/andP. by split.
      move: (technical (w ^ 2) H5).
      rewrite expn_eq0 andbT.
      move/eqP => H6.
      move: wordsize_neq0 => H7.
      by rewrite H6 in H7.
     dependent induction B2;last first.
      destruct c0;last by rewrite /= technical2 in x0.
      destruct c => //.
      dependent induction B2_1;last first.
       destruct c => //. by rewrite /= technical2 in x0.
      dependent induction B2_2;last first.
       destruct c => //. by rewrite /= technical2 in x0.
      rewrite -x /=.
      have H3 : size (rcons (delete arr i9) (access arr0 0)) = size arr. rewrite size_rcons size_delete // -addn1 -subn1 subnK //. by apply: sizeW.
      clear IHB2_1 IHB2_2 okB.
      rewrite -H3 in i2,i3.
      case_eq (w ^ 2 %/ 2 == size arr0) => H4.
       move: (sizeW arr0 i5) => H7. 
       move: (sizeW arr1 i7) => H8.
       case_eq (w ^ 2 %/ 2 == size arr1) => H5.
        have i10 : w ^ 2 %/ 2 <= size (behead arr0 ++ arr1).
         rewrite size_cat size_behead.
         have H6 : size arr1 <= (size arr0).-1 + size arr1. exact: leq_addl.
         apply: (leq_trans i7 H6).
        have i11 : size (behead arr0 ++ arr1) < 2 * w ^ 2.
         move/eqP: H4 => H4. move/eqP: H5 => H5.
         rewrite -H4 in H7.
         rewrite size_cat size_behead.
         rewrite -H4 -H5 addnC -subn1 addnBA //.
         apply/eqP/eqP.
         rewrite -addn1 mulnC muln2 -addnn subnK -/(leq _ _).
         have H6: w ^ 2 %/ 2 <= w ^ 2. exact: leq_div.
         apply: leq_add => //.
         move: (H7) => H9.
         rewrite -(ltn_add2r (w ^ 2 %/ 2)) in H7.
         exact: (ltn_trans H9 H7).
        (* rewrite -size_cat -(cons_head_behead arr0) // -catA size_cat /= [1 + size _]addnC addnA -addnBA // subnn addn0. *)
        have H9 : (rcons (delete arr i9) (access arr0 0)) ++ (behead arr0 ++ arr1) = (delete arr i9) ++ arr0 ++ arr1. rewrite cat_rcons -cat_cons (cons_head_behead arr0) //.
        rewrite -H3 subn1 [size arr0 + _]addnC -subn1 -addnBA;last first.
         rewrite -(ltn_add2r (size arr1)) add0n addnC in H7. exact: (ltn_trans H8 H7).
        rewrite -addnBA // subn1 [size arr1 + _]addnC -(size_behead arr0) -size_cat.
        rewrite (technical3 (count_one _));last first.
         rewrite -(cat_take_drop i9 arr) /count_one count_cat nth_cat size_take.
         case: ifP. case: ifP => H10. by rewrite ltnn. by rewrite H10.
         case: ifP;last by rewrite H.
         rewrite subnn nth0 /head /(count_mem _).
         case (drop i9 arr) => // b.
         destruct b => //.
         case (take i9 arr) => // b.
         destruct b => // /= l r.
         rewrite add0n addnA ltn_addr // ltn_addl //.
        rewrite count_delete /count_one -!count_cat -H9 count_cat.
        by exists (Good Black (bnode (Leaf (rcons (delete arr i9) (access arr0 0)) i2 i3) (Leaf (behead arr0 ++ arr1) i10 i11))).
       clear x.
       have H6 : size arr1 = (size (delete arr1 0)).+1. rewrite (size_delete H8) -subn1 -addn1 subnK //. 
       rewrite leq_eqVlt H5 H6 /= in i7.
       move : (ltnW i8) => i8'.
       rewrite H6 /= in i8'.
       have H9 : size (rcons (delete arr0 0) (access arr1 0)) = size arr0. rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
       rewrite -H9 in i5,i6.
       rewrite -H3 -H9 subn1 [size _ + size arr1]addnC -subn1 -addnBA;last first.
        rewrite H9. rewrite -(ltn_add2r (size arr1)) add0n addnC in H7. exact: (ltn_trans H8 H7).
       rewrite [size arr1 + _]addnC -addnBA // subn1 H6 -addn1 -subn1 -addnBA // subnn addn0.
       have H10 : (rcons (delete arr i9) (access arr0 0)) ++ (rcons (delete arr0 0) (access arr1 0)) ++ (delete arr1 0) = (delete arr i9) ++ arr0 ++ arr1.
        rewrite !cat_rcons -!catA drop1 take0 cat0s -cat_cons cons_head_behead // -cat_cons drop1 take0 cat_cons cat0s cons_head_behead //.
       rewrite technical3;last first.
        rewrite -(cat_take_drop i9 arr) /count_one count_cat nth_cat size_take.
        case: ifP. case: ifP => H11. by rewrite ltnn. by rewrite H11.
        case: ifP;last by rewrite H.
        rewrite subnn nth0 /head /(count_mem _).
        case (drop i9 arr) => // b.
        destruct b => //.
        case (take i9 arr) => // b.
        destruct b => // /= l r.
        rewrite add0n addnA ltn_addr // ltn_addl //.
       rewrite count_delete /count_one -!count_cat -H10 2!count_cat.
       by exists (Good Black (bnode (Leaf (rcons (delete arr i9) (access arr0 0)) i2 i3)
                                    (rnode (Leaf (rcons (delete arr0 0) (access arr1 0)) i5 i6)
                                           (Leaf (delete arr1 0) i7 i8')))).
      move: (sizeW arr0 i5) => H5. 
      move: (sizeW arr1 i7) => H6.
      have H7 : size arr0 = (size (delete arr0 0)).+1. rewrite (size_delete H5) -subn1 -addn1 subnK //. 
      clear x.
      rewrite leq_eqVlt H4 H7 /= in i5.
      rewrite H7 in i6.
      rewrite -H3 H7 subn1 [_.+1 + size arr1]addnC -subn1 -addnBA;last first.
       rewrite -H7. rewrite -(ltn_add2r (size arr1)) add0n addnC in H5. exact: (ltn_trans H6 H5).
      rewrite -addn1 addnA -addnBA // subnn addn0 [size arr1 + _]addnC.
      have H8 : (rcons (delete arr i9) (access arr0 0)) ++ (delete arr0 0) ++ arr1 = (delete arr i9) ++ arr0 ++ arr1.
       rewrite !cat_rcons -!catA drop1 take0 cat0s -cat_cons cons_head_behead //.
      rewrite technical3;last first.
       rewrite -(cat_take_drop i9 arr) /count_one count_cat nth_cat size_take.
       case: ifP. case: ifP => H11. by rewrite ltnn. by rewrite H11.
       case: ifP;last by rewrite H.
       rewrite subnn nth0 /head /(count_mem _).
       case (drop i9 arr) => // b.
       destruct b => //.
       case (take i9 arr) => // b.
       destruct b => // /= l r.
       rewrite add0n addnA ltn_addr // ltn_addl //.
      rewrite count_delete /count_one -!count_cat -H8 2!count_cat.
      by exists (Good Black (bnode (Leaf (rcons (delete arr i9) (access arr0 0)) i2 i3)
                                   (rnode (Leaf (delete arr0 0) i5 (ltnW i6))
                                          (Leaf arr1 i7 i8)))).
     (* B2 = Leaf *)
     case_eq (w ^ 2 %/ 2 == size arr0) => H3.
     move: (sizeW arr i2) => H4.
     move: (sizeW arr0 i) => H5.
     have i10 : w ^ 2 %/ 2 <= size ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0)).
      rewrite size_cat size_rcons !size_delete // -[_.-1]subn1 -[(_ - 1).+1]addn1 subnK //.
      have H6 : size arr <= size arr + (size arr0).-1. exact: leq_addr.
      exact: (leq_trans i2 H6).
     have i11 : size ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0)) < 2 * w ^ 2.
      move/eqP: H3 => H3. move/eqP: H2 => H2.
      move: (H4) => H7.
      rewrite H2 in H7.
      rewrite size_cat size_rcons !size_delete // -[_.-1]subn1 -[(_ - 1).+1]addn1 subnK // H2 -H3.
      rewrite -subn1 addnBA //.
      apply/eqP/eqP.
      rewrite -addn1 mulnC muln2 -addnn subnK -/(leq _ _).
       have H6: w ^ 2 %/ 2 <= w ^ 2. exact: leq_div.
       apply: leq_add => //.
      move: (H7) => H9.
      rewrite -(ltn_add2r (w ^ 2 %/ 2)) in H7.
      exact: (ltn_trans H9 H7).
     have H6 : size (rcons (delete arr i5) (access arr0 0)) = size arr. rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
     destruct c.
      rewrite -addnBA // subn1 /= -H6 -(size_delete H5) -size_cat addnC -addnBA;last first.
       rewrite -(cat_take_drop i5 arr) /count_one count_cat nth_cat size_take.
       case: ifP. case: ifP => H11. by rewrite ltnn. by rewrite H11.
       case: ifP;last by rewrite H.
       rewrite subnn nth0 /head /(count_mem _).
       case (drop i5 arr) => // b.
       destruct b => //.
       case (take i5 arr) => // b.
       destruct b => // /= l r.
       rewrite add0n addnA ltn_addr // ltn_addl //.
      rewrite count_delete addnC -count_cat.
      have H7 : rcons (delete arr i5) (access arr0 0) ++ delete arr0 0 = delete arr i5 ++ arr0.
       rewrite cat_rcons -cat_cons take0 drop1 cat_cons cat0s cons_head_behead //.
      rewrite -H7.
      by exists (Good Red (Leaf ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0)) i10 i11)).
((rcons (delete arr i5) (access arr0 0))

  {B' : near_tree (size (rcons (delete arr i5) (access arr0 0) ++ delete arr0 0)) ((count_mem true) ) (Param 0) Red | dflattenn B' = delete arr i5 ++ arr0}
     


     clear okB.
     move: (i2) => i2'.
     move: (i3) => i3'.
     rewrite -H6 in i2,i3.
     have i6 : (w ^ 2 %/ 2 <= size ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0))).
     rewrite size_cat size_rcons size_delete // size_delete //.


     have H6 : size arr0 = (size (delete arr0 0)).+1. rewrite (size_delete H5) -subn1 -addn1 subnK //.
     move: (i) => i'.
     move: (i4) => i4'.
     clear okB.
     rewrite H6 in i,i4.
                                     (Leaf (delete arr1 0) i7 i8')))).


     rewrite leq_eqVlt H6 in i.
     move : (ltnW i8) => i8'.
       rewrite H6 /= in i8'.
       have H9 : size (rcons (delete arr0 0) (access arr1 0)) = size arr0. rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
       rewrite -H9 in i5,i6.
       rewrite -H3 -H9 subn1 [size _ + size arr1]addnC -subn1 -addnBA;last first.
        rewrite H9. rewrite -(ltn_add2r (size arr1)) add0n addnC in H7. exact: (ltn_trans H8 H7).
       rewrite [size arr1 + _]addnC -addnBA // subn1 H6 -addn1 -subn1 -addnBA // subnn addn0.
       have H10 : (rcons (delete arr i9) (access arr0 0)) ++ (rcons (delete arr0 0) (access arr1 0)) ++ (delete arr1 0) = (delete arr i9) ++ arr0 ++ arr1.
        rewrite !cat_rcons -!catA drop1 take0 cat0s -cat_cons cons_head_behead // -cat_cons drop1 take0 cat_cons cat0s cons_head_behead //.
       rewrite technical3;last first.
        rewrite -(cat_take_drop i9 arr) /count_one count_cat nth_cat size_take.
        case: ifP. case: ifP => H11. by rewrite ltnn. by rewrite H11.
        case: ifP;last by rewrite H.
        rewrite subnn nth0 /head /(count_mem _).
        case (drop i9 arr) => // b.
        destruct b => //.
        case (take i9 arr) => // b.
        destruct b => // /= l r.
        rewrite add0n addnA ltn_addr // ltn_addl //.
       rewrite count_delete /count_one -!count_cat -H10 2!count_cat.
     



       About size_behead.

 (behead arr1)) _ _)
                                                (behead arr0 ++ arr1) i10 i11))).


 -addnBA.
                count_cat -!/(count_one _) -count_delete size_cat [_.-1 + size arr1]addnC -subn1 addnBA // addnBA
        rewrite [size _ + size _]addnC -count_cat -!/(count_one _)  /=;last first.


        move => wit.
        exists wit.
        rewrite /=.
        


          case i9;last first.
          intros.
          destruct arr => //.
          rewrite drop0 take0 add0n /=.
          case arr => //.
          intros.
               -(cons_head_behead (drop _ _)) /= //.
            by rewrite ltnn. by rewrite H10.
        rewrite size_take.
        case: ifP.
        apply/nthP.
        About nth_take.
        rewrite -(nth_take false).

        rewrite -subn_eq0.
        re#htwrite -leq_sub2r.
          case (nth false arr i9) => /=.
          rewrite subn1 addn1 /=.
           rewrite -addnBA.
           rewrite -subSS.

        rewrite subn2r.
        About count_delete.
        arr = delete arr i9 + 
         elim arr => /=. by case i9 => /=.
         intros.
          
          case arr => /= //; by case.
nth false (a :: l) n.+1

         
  jj       rewrite /nth.
         case: (nth false arr i9) => // /=.
         
        move => wit.
        exists wit.
         subSn.
         => wit.

        
        Check 
(behead arr0 ++ arr1)
(size arr0 + size arr1) - 1



         rewrite H4 H5.
         apply: sizeW.
         About leq_subLR.
         rewrite 

         subnDA.
         addnBA.

         rewrite subn1. subSS.




      delete 


                (Leaf  _ _) (Leaf sr _ _))

(delete arr0 0) ++ [access arr1 0]
(delete arr1 0)

      

      c => // /=;last first.
     have H5 : size arr = (size (delete arr i5)) + 1.
      rewrite (size_delete H) -subn1 subnK //.
      by apply: sizeW.
     rewrite H5 addnC addnA -addnBA // subnn addn0 addnC -size_cat (technical3 (count_one arr) _ _).
     have H6 : count_one arr - nth false arr i5 = count_one (delete arr i5). by rewrite count_delete.
     rewrite H6 -count_cat.
     exists (Good Black (Leaf ((delete arr i5) ++ arr0) _ _)).
     About subn_if_gt.
     rewrite subnDA.
     rewrite H5 addnC addnA -addnBA // subnn addn0 addnC -size_cat.
     rewrite subnn.
     destruct d.
     case: B2;last first.
     case B2;last first.
     intros.
     inversion B2;last first.
     rewrite /delete take_cat.
      case: ifP => // H3.
       rewrite take_o.versize //.
     dependent inversion B2.

      rewrite -[w ^ 2]mulKn.
      rewrite (mulKn (w ^ 2) _ 2). //.


     apply: conj.
     Print conj.
     apply/implyP.
     move/andP.













     move: (negbT H3).
     rewrite -leqNgt => H2.
     rewrite nth_default /= // !subn0.
     exists (Good Black (Leaf arr i i0)).
     by rewrite -delete_oversize /=.
    case_eq (i1 < s1 + s2) => H; last first.
     move: (negbT H).
     rewrite -leqNgt => H2.
     rewrite daccess_default // /= !subn0.
     exists (Good c (Node i i0 B1 B2)).
     rewrite -delete_oversize /= //.
     by rewrite size_cat !dflatten_sizeK.
    

     rewrite /=. /delete drop_oversize.

    rewrite H /= orbF.

      
      About expn_gt0.
      move/eqP: i0.
      case_eq w => /=.
      rewrite exp0n.
    (* w ^ 2 %/2 < size arr.  -> 
     *)
    (* どうすっぺ *)

    match num == (w ^ 2) %/ 2 with
    | true =>
      match B with
      | Leaf s _ _ => Good Black (Leaf (delete s i) _ _)
      | Node s1 o1 s2 o2 (Param 0) Black Black Red okl okr (Leaf sl _ _) (Leaf sr _ _) =>
        Good c (Leaf ((delete sl i) ++ sr) _ _)
      | Node s1 o1 s2 o2 d cl cr _ okl okr l r =>
        (* size s >= w ^ 2 *)
        if (daccess l i) == ~~ (daccess r 0)
        then proj1_sig (balanceR c (fst (proj1_sig (bset l i))) (ddelete r 0) okl _)
        else proj1_sig (balanceR c l (ddelete r 0) okl _)
      end
    | false =>
      match B with
      | Leaf s _ _ => Good Black (Leaf (delete s i) _ _)
      | Node s1 o1 s2 o2 d cl cr _ okl okr l r =>
        proj1_sig (balanceL c (ddelete l i) r _ okr)
      end
    end.


      (* if i < s1 *)
      (* then if num == (w ^ 2) %/ 2 *)
      (*      then if (daccess l i) <> (daccess r 0) *)
      (*           then proj1_sig (balanceR c (fst (proj1_sig (bset l i))) (ddelete r 0 w) okl _) *)
      (*           else proj1_sig (balanceR c l (ddelete r 0 w) okl _) *)
      (*      else proj1_sig (balanceL c (ddelete l i w) r _ okr) *)
      (* else proj1_sig (balanceR c l (dinsert' r b (i - s1) w) okl _) *)
    end.

End delete.


(* 
Extraction dinsert'_func.
Extraction bset_func. 
*)
