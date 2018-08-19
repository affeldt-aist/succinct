From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program JMeq set_clear.

Set Implicit Arguments.

Variable w : nat.
Axiom wordsize_gt1: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. apply ltnW. exact wordsize_gt1. Qed.

Lemma wordsize_neq0: w != 0.
Proof. rewrite -lt0n. exact wordsize_gt0. Qed.

Lemma wordsize_sqrn_gt2 : w ^ 2 > 2.
Proof.
  case_eq w => n. move: wordsize_neq0. by rewrite n.
  case_eq n => n' H. move/eqP: (ltn_eqF wordsize_gt1). by rewrite H.
  move => H'.
  rewrite -[n'.+2]addn2 sqrnD -!mulnn !muln2 -!addnn add2n addnC !addnA.
  apply/eqP.
  rewrite addnC subnDA.
  by compute.
Qed.

Lemma wordsize_sqrn_gt0 : w ^ 2 > 0.
Proof. exact: (ltnW (ltnW wordsize_sqrn_gt2)). Qed.

Lemma wordsize_sqrn_div2_neq0 : (w ^ 2 %/ 2 <> 0).
Proof.
  case_eq w => n. move: wordsize_neq0. by rewrite n.
  move => H1 H2.
  move: (divn_eq (n.+1 ^ 2) 2).
  rewrite H2 mul0n add0n.
  case_eq n => [H3|n']. rewrite H3 in H1. move/eqP: (ltn_eqF wordsize_gt1). by rewrite H1.
  move => H3 H4.
  rewrite -H3 -H1 in H4.
  have H5 : (0 < 2) => //.
  rewrite -(ltn_mod (w ^ 2) 2) -H4 in H5.
  move: wordsize_sqrn_gt2.
  rewrite ltnNge.
  move: (ltnW H5) => H6.
  by rewrite H6 /=.
Qed.

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
    | Black, n => n.+1
    | _, _ => d
    end.

  (* Definition dec_black d c := *)
  (*   match c, d with *)
  (*   | Black, Param n => Param n.-1 *)
  (*   | _, _ => d *)
  (*   end. *)

  (* Axiom technical2 : forall(d : param nat), (inc_black d Black) <> Param 0. *)
  (* Axiom technical3 : forall(d0 d : param nat), inc_black d0 Black = inc_black d Black -> d0 = d. *)

  (* Definition app_param (A B : Type) (f : A -> B) (x : param A) := *)
  (*   let: Param x := x in Param (f x). *)

  (* work around for program fixpoint *)
  Definition count_one arr := count_mem true arr.

  Inductive tree : nat -> nat -> nat -> color -> Type :=
  | Leaf : forall (arr : seq bool),
      (w ^ 2) %/ 2 <= (size arr) ->
      2 * (w ^ 2) > (size arr) ->
      tree (size arr) (count_one arr) 0 Black
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

  Inductive near_tree : nat -> nat -> nat -> color -> Type :=
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

  Lemma dflatten_countK {n m d c} (B : tree n m d c) : count_one (dflatten B) = m.
  Proof.
    elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
    rewrite /count_one in IHl,IHr.
    by rewrite /count_one count_cat IHl IHr.
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

  Definition is_leaf {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => true
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => false
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

  Lemma technical1 : forall(n : nat),n * 2 <= n -> n == 0.
  Proof.
    move => n.
    move/eqP.
    rewrite muln2 -addnn -addnBA // subnn addn0.
    by move/eqP.
  Qed.

  Lemma size_of_node {n m d c} (tr : tree n m d c) : is_node tr -> n >= w ^ 2 %/ 2 * 2.
  Proof.
    dependent induction tr => // H.
    case_eq (is_node tr1) => H1.
     move: (IHtr1 H1) (leq0n s2) => leq1 leq2.
     move: (leq_add leq1 leq2).
     by rewrite addn0.
    destruct tr1 => //.
    case_eq (is_node tr2) => H2.
     move: (IHtr2 H2) (leq0n (size arr)) => leq1 leq2.
     move: (leq_add leq1 leq2).
     by rewrite addn0 addnC.
    clear H H1.
    destruct tr2 => //;last first. by rewrite /= in H2.
    clear IHtr1 IHtr2 H2.
    rewrite addnC.
    rewrite -(leq_add2r (size arr)) in i3.
    rewrite -(leq_add2l (w ^ 2 %/ 2)) addnn -muln2 in i1.
    exact: (leq_trans i1 i3).
  Qed.

  Lemma sizeW (arr : seq bool) : w ^ 2 %/ 2 <= size arr -> 0 < size arr.
  Proof.
    move/eqP: wordsize_sqrn_div2_neq0.
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

    (* proof_irrevance. *)

  Lemma addsubnC : forall(a b c : nat),a >= c -> a + b - c = a - c + b.
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

  Lemma leq_size_catr (a : nat) (arr0 arr1 : seq bool) : a <= size arr1 -> a <= size (arr0 ++ arr1).
  Proof.
    rewrite size_cat.
    move => leq.
    apply: (leq_trans leq (leq_addl (size arr0) (size arr1))).
  Qed.

  Lemma ltn_size_cat (a b : nat) (arr0 arr1 : seq bool) : size arr0 < a ->
                                                          size arr1 < b ->
                                                          size (arr0 ++ arr1) < a + b.
  Proof.
    rewrite size_cat.
    move => ltn1 ltn2.
    rewrite -(ltn_add2r b) in ltn1.
    rewrite -(ltn_add2l (size arr0)) in ltn2.
    exact: (ltn_trans ltn2 ltn1).
  Qed.

  Lemma ltn_size_catb (a : nat) (arr0 arr1 : seq bool) : size arr0 < a ->
                                                         size arr1 < a ->
                                                         size (arr0 ++ arr1) < a.*2.
  Proof.
    move => H1 H2.
    rewrite -addnn.
    exact: (ltn_size_cat _ _ arr0 arr1 H1 H2).
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
    by rewrite cats0.
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

  Lemma divn2n0 {a} : (a %/ 2 == a) = (a == 0).
  Proof.
    case a => // a'.
    case a' => // a''.
    by rewrite -addn1 addn_eq0 addn1 {2}(divn_eq a''.+2 2) muln2 -addnn -addnA -{1}[a''.+2 %/ 2]addn0 eqn_add2l -addn1 andbF addn1 -addn2 divnDr // divnn /= eq_sym !addn_eq0 andbF andFb.
  Qed.

  Lemma leq_divn2n_mul2 : forall(a : nat),a > 0 -> a %/ 2 + a %/ 2 < 2 * a.
  Proof.
    move => // a H0.
    move: (leq_div a 2).
    rewrite leq_eqVlt.
    case/orP. rewrite divn2n0. move/eqP => H1. by rewrite H1 in H0.
    by rewrite mulnC addnn -muln2 ltn_mul2r /=.
  Qed.

  Lemma leq_addln : forall(a b c: nat), a <= b -> a <= b + c.
  Proof.
    move => a b c leq1.
    move: (leq0n c) => leq2.
    rewrite -(leq_add2l b) addn0 in leq2.
    exact: (leq_trans leq1 leq2).
  Qed.

  Lemma leq_addrn : forall(a b c: nat), a <= c -> a <= b + c.
  Proof. move => a b c. rewrite addnC. exact: (leq_addln a c b). Qed.

  Lemma ltn_addrn : forall(a b c: nat), a < c -> a < b + c.
  Proof.
    move => a b c ltn1.
    move: (leq0n b) => leq2.
    rewrite -(leq_add2r c) add0n in leq2.
    rewrite leq_eqVlt in leq2.
    case/orP: leq2 => [|ltn2]. move/eqP => H. by rewrite -H.
    exact: (ltn_trans ltn1 ltn2).
  Qed.

  Lemma ltn_addln : forall(a b c: nat), a < b -> a < b + c.
  Proof. move => a b c. rewrite addnC. exact: (ltn_addrn a c b). Qed.

  Lemma delete0_behead (arr : seq bool) : delete arr 0 = behead arr.
  Proof. case arr => /= // b l. by rewrite /delete take0 drop1 cat0s /=. Qed.

  Lemma sizeW' {s o d c} (tr : tree s o d c) : s > 0.
  Proof.
    move: (size_of_node tr).
    rewrite /= muln2 -addnn => H.
    destruct tr. exact: sizeW => //.
    move/implyP : H => /= H.
    move/eqP: wordsize_sqrn_div2_neq0.
    rewrite -lt0n => ltn1.
    move: (ltn_addrn 0 (w ^ 2 %/ 2) _ ltn1) => ltn2.
    rewrite leq_eqVlt in H.
    case/orP: H. move/eqP => H. by rewrite -H.
    move => H.
    exact: (ltn_trans ltn2 H).
  Qed.

  Inductive near_tree' : nat -> nat -> nat -> color -> Type := 
  | Stay : forall {s o d},
      near_tree s o d.+1 Black -> near_tree' s o d Black
  | Down : forall {s o d},
      near_tree s o d Black -> near_tree' s o d Black.

  Definition dflattenn' {s o d c} (tr : near_tree' s o d c) :=
    match tr with
    | Stay _ _ _ t => dflattenn t
    | Down _ _ _ t =>  dflattenn t
   end.

  Definition dflatten' {n m d c} (tr : tree n m d c) :=
    match tr with
    | Leaf s _ _ => s
    | Node _ _ _ _ _ _ _ _ _ _ l r => dflatten l ++ dflatten r
    end.

  Lemma dflatten_is_dflatten' {n m d c} (tr : tree n m d c) : dflatten tr = dflatten' tr.
  Proof. by destruct tr. Qed.

  Lemma rnode_is_not_leaf {s o d} (tr : tree s o d Red) : ~~ is_leaf tr.
  Proof. dependent destruction tr => //. Qed.

  Lemma bnode_is_color_ok {s o d c} (tr : near_tree s o d Black) : color_ok c (fix_color tr).
  Proof. destruct c => //. dependent destruction tr => //. Qed.

  Lemma dflatten_rb {s1 o1 s2 o2 d} (B1 : tree s1 o1 d Black) (B2 : tree s2 o2 d Black) : dflatten (bnode B1 B2)~= dflatten (rnode B1 B2).
  Proof. by rewrite /=. Qed.

  Lemma leq_access_count {s o d c} : forall(B : tree s o d c), forall(i : nat) , i < s -> daccess B i <= o.
  Proof.
    move => B.
    elim B => /=. intros. exact: leq_nth_count.
    move => s1 o1 s2 o2 d' cl cr c' ? ? l IHl r IHr.
    move => i H.
    case: ifP => H'. apply: leq_addln (IHl i H').
    apply: leq_addrn.
    move: (IHr (i - s1)).
    rewrite -(ltn_add2r s1) subnK ;last by rewrite leqNgt H' /=.
    rewrite addnC => H''.
    exact: (H'' H).
  Qed.


  (* Axiom pos_tree_is_not_leaf : forall(s o : nat) (d' d : param nat) (c : color) (B : tree s o d' c), (inc_black d Black) = d' -> is_node B. *)
      

  Definition rotateR {s1 s2 o1 o2 d} (B1 : tree s1 o1 d Black) (B2 : tree s2 o2 d Red) : { B : tree (s1 + s2) (o1 + o2) (inc_black d Black) Black | wordsize_ok B /\ dflatten B = dflatten B1 ++ dflatten B2 }.

    dependent destruction B2.
    destruct cl,cr => //.
    rewrite !addnA.
    exists (bnode (rnode B1 B2_1) B2_2).
    by rewrite /= catA.
  Defined.

  Definition black_of_red {s o d} (B : tree s o d Red) : { B' : tree s o (inc_black d Black) Black | dflatten B' = dflatten B }.

    dependent destruction B.
    destruct cl,cr => //.
    by exists (bnode B1 B2).
  Defined.

  Lemma pos_tree_is_not_leaf {num ones d c} (B : tree num ones d.+1 c) : ~~ is_leaf B.
  Proof. dependent inversion B  => //. Qed.

  Lemma node_is_not_leaf  {num ones d c} (B : tree num ones d c) : is_node B -> ~~ is_leaf B.
  Proof. destruct B => //. Qed.

  Lemma bzero_tree_is_leaf {num ones} (B : tree num ones 0 Black) : ~~ is_node B.
  Proof. dependent destruction B => //. Qed.

  Lemma ltn_pred n : n > 0 -> n.-1 < n.
  Proof. case n => //. Qed.

  Definition makeBadL {s1 s2 o1 o2 d} (l : tree s1 o1 d Red) (r : tree s2 o2 d Black) : { tr : near_tree (s1 + s2) (o1 + o2) d Red | dflattenn tr = dflatten l ++ dflatten r }.

    move: r.
    dependent inversion l as [|? ? ? ? ? cl cr ? ? ? ll lr seql oeql heql ceql ] => //.
    destruct cl,cr => //. rewrite ceql /= in heql.
    move: ll lr. rewrite heql /= => ll lr r.
    exists (Bad ll lr r).
    by rewrite /= catA.
  Defined.

  Definition makeBadR {s1 s2 o1 o2 d} (l : tree s1 o1 d Black) (r : tree s2 o2 d Red) : { tr : near_tree (s1 + s2) (o1 + o2) d Red | dflattenn tr = dflatten l ++ dflatten r }.

    move: l.
    dependent inversion r as [|? ? ? ? ? cl cr ? ? ? rl rr seqr oeqr heqr ceqr ] => //.
    destruct cl,cr => //. rewrite ceqr /= in heqr.
    move: rl rr. rewrite heqr /= => rl rr l.
    rewrite !addnA.
    exists (Bad l rl rr).
    by rewrite /= catA.
  Defined.

  Definition delete_leaves3
             (arrl arrrl arrrr : seq bool)
             (leql : w ^ 2 %/ 2 <= size arrl)
             (ueql : size arrl < 2 * w ^ 2)
             (leqrl : w ^ 2 %/ 2 <= size arrrl)
             (ueqrl : size arrrl < 2 * w ^ 2)
             (leqrr : w ^ 2 %/ 2 <= size arrrr)
             (ueqrr : size arrrr < 2 * w ^ 2)
             (i : nat) :
    {B' : tree (size arrl + (size arrrl + size arrrr) - (i < size arrl + size arrrl + size arrrr))
               (count_one arrl + (count_one arrrl + count_one arrrr) - nth false (arrl ++ arrrl ++ arrrr) i) 1 Black | dflatten B' = delete (arrl ++ arrrl ++ arrrr) i}.

    move : (sizeW _ leql) (sizeW _ leqrl) (sizeW _ leqrr) => GUARDL GUARDRL GUARDRR.
    move: (ltn_addrn 0 (size arrrl) _ GUARDRR) => GUARDR.
    rewrite nth_cat delete_cat.
    case Hl : (i < size arrl).
    rewrite -[size _ + size _ + size _]addnA (ltn_addln i (size arrl) ((size arrrl) + (size arrrr)) Hl).
     case bcl : (w ^ 2 %/ 2 == size arrl).
      rewrite -(size_rcons_delete i (access arrrl 0)) // in leql,ueql.
      case bcrl : (w ^ 2 %/ 2 == size arrrl).
       case bcrr : (w ^ 2 %/ 2 == size arrrr).
        have ueqrr' : size ((delete arrrl 0) ++ arrrr) < 2 * w ^ 2.
         move/eqP in bcrl. move/eqP in  bcrr.
         rewrite size_cat size_delete // -bcrl -bcrr addnC -subn1 !addnBA;last by rewrite -bcrl in GUARDRL.
         rewrite -(ltn_add2r 1) subnK;last by rewrite -bcrl -bcrr in GUARDR.
         by rewrite addn1 (leqW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
        rewrite [size _ + _ - _]addsubnC //.
        rewrite [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
        rewrite count_delete /count_one -!count_cat catA
                (size_delete1 i) Hl /= -addnBA // subnn addn0 -!size_cat catA
                -(cat_head_behead (delete arrl i)) // -catA count_cat size_cat.
        by exists (bnode (Leaf (rcons (delete arrl i) (access arrrl 0)) leql ueql) (Leaf ((delete arrrl 0) ++ arrrr) (leq_size_catr _ (delete arrrl 0) arrrr leqrr) ueqrr')).
       rewrite leq_eqVlt bcrr (size_delete1 0) /= GUARDRR /= addn1 in leqrr.
       rewrite (size_delete1 0) GUARDRR /= addn1 /= in ueqrr.
       have leql' : w ^ 2 %/ 2 <= size ((delete arrl i) ++ (rcons arrrl (access arrrr 0))). rewrite size_cat size_rcons leq_addrn //;last exact: leqW.
       have ueql' : 2 * w ^ 2  > size ((delete arrl i) ++ (rcons arrrl (access arrrr 0))).
        move/eqP: bcrl => bcrl. move/eqP: bcl => bcl.
        rewrite size_cat size_rcons size_delete // -bcrl -bcl addnC -subn1 // -2!addn1 -addnA subnK //;last by rewrite -bcrl in GUARDRL.
        by rewrite addnC addnA addn1 (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0).
       rewrite [size _ + _ - _]addsubnC // [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
       rewrite count_delete /count_one -!count_cat catA (size_delete1 i) Hl /= -addnBA // subnn addn0 -!size_cat -(cons_head_behead arrrr) //
               -delete0_behead -cat_rcons catA size_cat -catA -cat_rcons catA count_cat.
       exists (bnode (Leaf ((delete arrl i) ++ (rcons arrrl (access arrrr 0))) leql' ueql') (Leaf (delete arrrr 0) leqrr (ltnW ueqrr))).
       by rewrite /= -/(nth false _ 0) -/(access _ _) catA take0 drop1 cats0 -catA.
      rewrite leq_eqVlt bcrl (size_delete1 0) GUARDRL /= addn1 in leqrl.
      rewrite (size_delete1 0) GUARDRL /= addn1 in ueqrl.
      rewrite /count_one -!count_cat catA -(size_rcons_delete i (access arrrl 0)) // addnA addnC addnA -addnBA // subn1 -(size_delete GUARDRL) -addnA addnC -addnA
              !count_cat [(count_mem _) _ + _]addnC addsubnC;last apply: leq_addrn leq_nth_count.
      rewrite -addnBA -/(count_one arrl);last exact: leq_nth_count.
      rewrite count_delete [(count_mem _) _ + _]addnC -count_cat catA -(cat_head_behead (delete arrl i)) //.
      rewrite count_cat -addnA.
      exists (bnode (Leaf (rcons (delete arrl i) (access arrrl 0)) leql ueql) (rnode (Leaf (delete arrrl 0) leqrl (ltnW ueqrl)) (Leaf arrrr leqrr ueqrr))).
      by rewrite /= -/(nth false _ 0) -/(access _ _) catA cat_head_behead // -catA.
     rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
     rewrite addnC -addnBA // subn1 -(size_delete Hl) addnC addsubnC;last exact: leq_nth_count.
     rewrite count_delete.
     by exists (bnode (Leaf (delete arrl i) leql (ltnW ueql)) (rnode (Leaf arrrl leqrl ueqrl) (Leaf arrrr leqrr ueqrr))).
    rewrite nth_cat delete_cat.
    case Hrl : (i - size arrl < size arrrl).
    rewrite ltn_addr;last rewrite -(ltn_add2r (size arrl)) subnK in Hrl;last rewrite leqNgt Hl => //;last by rewrite addnC.
     case bcrl : (w ^ 2 %/ 2 == size arrrl).
      case bcrr : (w ^ 2 %/ 2 == size arrrr).
       have ueqrr' : size ((delete arrrl (i - size arrl)) ++ arrrr) < 2 * w ^ 2.
        move/eqP in bcrl. move/eqP in  bcrr.
        rewrite size_cat size_delete // -bcrl -bcrr addnC -subn1 !addnBA;last by rewrite -bcrl in GUARDRL.
        rewrite -(ltn_add2r 1) subnK;last by rewrite -bcrl -bcrr in GUARDR.
        by rewrite addn1 (leqW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
       rewrite -addnBA // [size _ + _ - _]addsubnC //.
       rewrite -addnBA;last rewrite leq_addln //;last exact: leq_nth_count.
       rewrite [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
       rewrite count_delete /count_one -!count_cat subn1 -(size_delete Hrl) /=.
       rewrite -size_cat count_cat.
       by exists (bnode (Leaf arrl leql ueql) (Leaf ((delete arrrl (i - size arrl)) ++ arrrr) (leq_size_catr _ (delete arrrl (i - size arrl)) arrrr leqrr) ueqrr')).
      rewrite -(size_rcons_delete _ (access arrrr 0) Hrl) /= in leqrl,ueqrl.
      rewrite leq_eqVlt bcrr (size_delete1 0) GUARDRR /= addn1 in leqrr,ueqrr.
      rewrite addnA addsubnC;last by rewrite ltn_addrn //.
      rewrite -addnBA // subn1 -(size_delete Hrl) /= -addnA.
      rewrite [count_one _ + (_ + _)]addnA addsubnC;last rewrite leq_addrn //;last exact: leq_nth_count.
      rewrite -addnBA;last exact: leq_nth_count.
      rewrite count_delete -!size_cat -!count_cat -catA count_cat -(cat_head_behead (delete _ _)) // 2!size_cat count_cat.
      by exists (bnode (Leaf arrl leql ueql) (rnode (Leaf (rcons (delete arrrl (i - size arrl)) (access arrrr 0)) leqrl ueqrl) (Leaf (delete arrrr 0) leqrr (ltnW ueqrr)))).
     rewrite leq_eqVlt bcrl (size_delete1 (i - size arrl)) Hrl /= addn1 in leqrl,ueqrl.
     rewrite -addnBA // [size _ + _ - _]addsubnC //.
     rewrite -addnBA;last rewrite leq_addln //;last exact: leq_nth_count.
     rewrite [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
     rewrite count_delete /count_one -!count_cat subn1 -(size_delete Hrl) /= 2!count_cat.
     by exists (bnode (Leaf arrl leql ueql) (rnode (Leaf (delete arrrl (i - size arrl)) leqrl (ltnW ueqrl)) (Leaf arrrr leqrr ueqrr))).
    case Hrr : (i - size arrl - size arrrl < size arrrr).
     move: (Hrr) => Hrr'.
     rewrite -(ltn_add2r (size arrrl + size arrl)) addnA subnK in Hrr';last by rewrite leqNgt Hrl. 
     rewrite subnK in Hrr';last by rewrite leqNgt Hl.
     rewrite addnA addnC [size arrrr + _]addnC addnA in Hrr'.
     rewrite Hrr' /=.
     case bcrr : (w ^ 2 %/ 2 == size arrrr).
      case bcrl : (w ^ 2 %/ 2 == size arrrl).
       move: (leq_size_catr _ (delete arrrr (i - size arrl - size arrrl)) arrrl leqrl) => leqrr'.
       rewrite size_cat addnC -size_cat in leqrr'.
       have ueqrr' : size (arrrl ++ delete arrrr (i - size arrl - size arrrl)) < 2 * w ^ 2.
        move/eqP in bcrl. move/eqP in  bcrr.
        rewrite size_cat size_delete // -bcrl -bcrr addnC -subn1 -addsubnC;last by rewrite -bcrl in GUARDRL.
        rewrite -(ltn_add2r 1) subnK;last by rewrite -bcrl -bcrr in GUARDR.
        by rewrite addn1 (leqW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
       rewrite -!addnBA //;last rewrite leq_addrn //;last exact: leq_nth_count;last exact: leq_nth_count.
       rewrite count_delete /count_one -!count_cat subn1 -(size_delete Hrr) /= -size_cat count_cat.
       by exists (bnode (Leaf arrl leql ueql) (Leaf (arrrl ++ (delete arrrr (i - size arrl - size arrrl))) leqrr' ueqrr')).
      rewrite leq_eqVlt bcrl (size_delete1 (size arrrl).-1) ltn_pred // addn1 /= in leqrl,ueqrl.
      have leqrr' : w ^ 2 %/ 2 <= size ((access arrrl (size arrrl).-1) :: (delete arrrr (i - size arrl - size arrrl))). rewrite /= size_delete // prednK //.
      have ueqrr' : size ((access arrrl (size arrrl).-1) :: (delete arrrr (i - size arrl - size arrrl))) < 2 * w ^ 2. rewrite /= size_delete // prednK //.
      rewrite -!addnBA //;last exact: leq_addrn leq_nth_count => //;last exact: leq_nth_count.
      rewrite count_delete -count_cat.
      rewrite subn1 -(size_delete Hrr) -size_cat -cat_last_belast // size_cat count_cat.
      by exists (bnode (Leaf arrl leql ueql) (rnode (Leaf (delete arrrl (size arrrl).-1) leqrl (ltnW ueqrl)) (Leaf ((access arrrl (size arrrl).-1) :: (delete arrrr (i - size arrl - size arrrl))) leqrr' ueqrr'))).
      rewrite leq_eqVlt bcrr (size_delete1 (i - size arrl -size arrrl)) Hrr /= addn1 in leqrr,ueqrr.
      rewrite -!addnBA //;last rewrite leq_addrn //;last exact: leq_nth_count;last exact: leq_nth_count.
      rewrite count_delete /count_one -!count_cat subn1 -(size_delete Hrr) /= 2!count_cat.
      by exists (bnode (Leaf arrl leql ueql) (rnode (Leaf arrrl leqrl ueqrl) (Leaf (delete arrrr (i - size arrl - size arrrl)) leqrr (ltnW ueqrr)))).
     move: (Hrr) => Hrr'.
     rewrite nth_default;last by rewrite leqNgt; move/negP/negP in Hrr.
     rewrite -(ltn_add2r (size arrrl + size arrl)) addnA subnK in Hrr;last by rewrite leqNgt Hrl. 
     rewrite subnK in Hrr;last by rewrite leqNgt Hl.
     rewrite addnA addnC [size arrrr + _]addnC addnA in Hrr.
     rewrite Hrr /= !subn0.
     rewrite /delete drop_oversize //;last by apply: leqW; rewrite leqNgt Hrr'.
     rewrite cats0 take_oversize //;last by rewrite leqNgt Hrr'.
     by exists (bnode (Leaf arrl leql ueql) (rnode (Leaf arrrl leqrl ueqrl) (Leaf arrrr leqrr ueqrr))).
  Defined.

  Definition delete_leaves2
             (arrl arrr : seq bool)
             (leql : w ^ 2 %/ 2 <= size arrl)
             (ueql : size arrl < 2 * w ^ 2)
             (leqr : w ^ 2 %/ 2 <= size arrr)
             (ueqr : size arrr < 2 * w ^ 2)
             (i : nat) :
  {B' : near_tree (size arrl + size arrr - (i < size arrl + size arrr))
      (count_one arrl + count_one arrr - nth false (arrl ++ arrr) i) 0 Black | dflattenn B' = delete (arrl ++ arrr) i}.

    rewrite delete_cat nth_cat.
    move: (sizeW _ leql) (sizeW _ leqr) => GUARDL GUARDR.
    move/eqP: wordsize_sqrn_div2_neq0. rewrite -lt0n => GUARD1. move: (ltn_addrn 0 (w ^ 2 %/ 2) _ GUARD1) => GUARD2.
    case: ifP => [Hl|Hr].
     rewrite ltn_addln //.
     case bcl : (w ^ 2 %/ 2 == size arrl).
      case bcr : (w ^ 2 %/ 2 == size arrr).
       move/eqP in bcl. move/eqP in bcr.
       have ueq : size ((rcons (delete arrl i) (access arrr 0)) ++ (delete arrr 0)) < 2 * w ^ 2.
        rewrite size_cat size_rcons !size_delete // -bcl -bcr -subn1 -2!addn1 subnK // addnBA // subnK //.
        exact: (ltnW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
       have leq : size (rcons (delete arrl i) (access arrr 0) ++ delete arrr 0) >= w ^ 2 %/ 2.
        rewrite size_cat size_rcons !size_delete // -[_.-1]subn1 -[(_ - 1).+1]addn1 subnK //.
        exact: leq_addln => //.
       rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat addsubnC;last exact: leq_nth_count.
       rewrite count_delete -count_cat -cat_head_behead //.
       by exists (Good Black (Leaf ((rcons (delete arrl i) (access arrr 0)) ++ (delete arrr 0)) leq ueq)).
      rewrite leq_eqVlt bcr (size_delete1 0) GUARDR /= addn1 in leqr,ueqr.
      rewrite -(size_rcons_delete i (access arrr 0)) // in leql,ueql.
      rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat addsubnC;last exact: leq_nth_count.
      rewrite count_delete -count_cat -cat_head_behead // count_cat size_cat.
      by exists (Good Black (rnode (Leaf (rcons (delete arrl i) (access arrr 0)) leql ueql) (Leaf (delete arrr 0) leqr (ltnW ueqr)))).
     rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
     rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC addsubnC;last exact: leq_nth_count.
     rewrite count_delete.
     by exists (Good Black (rnode (Leaf (delete arrl i) leql (ltnW ueql)) (Leaf arrr leqr ueqr))).
    case Hrl : (i < size arrl + size arrr).
     case bcr : (w ^ 2 %/ 2 == size arrr).
      case bcl : (w ^ 2 %/ 2 == size arrl).
       move/eqP in bcl. move/eqP in bcr.
       have ueq : size (arrl ++ (delete arrr (i - (size arrl)))) < 2 * w ^ 2.
        rewrite size_cat size_delete;last rewrite -(ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //; last by rewrite addnC Hrl.
        rewrite -bcl -bcr -(ltn_add2r 1) -subn1 addnBA // subnK;last by apply: ltn_addrn.
        rewrite addn1. exact: (leqW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
       have leq : size (arrl ++ (delete arrr (i - (size arrl)))) >= w ^ 2 %/ 2.
        rewrite size_cat size_delete;last rewrite -(ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //; last by rewrite addnC Hrl.
        rewrite -bcl -bcr -(leq_add2r 1) -subn1 addnBA // subnK;last by apply: ltn_addrn.
        rewrite addn1. by rewrite -(ltn_add2r (w ^ 2 %/ 2)) add0n in GUARD1.
       rewrite -addnBA /= // subn1 [size arrr](size_delete1 (i - size arrl)) -[i - _ < _](ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //.
       rewrite addnC in Hrl. rewrite Hrl /= -subn1 -addnBA // subnn addn0 -addnBA;last by exact: leq_nth_count.
       rewrite count_delete -count_cat -size_cat.
       by exists (Good Black (Leaf (arrl ++ (delete arrr (i - (size arrl)))) leq ueq)).
      rewrite leq_eqVlt bcl (size_delete1 (size arrl).-1) ltn_pred // addn1 /= in leql,ueql.
      have leqr' : w ^ 2 %/ 2 <= size ((access arrl (size arrl).-1) :: (delete arrr (i - size arrl))).
       rewrite /= size_delete //; last rewrite -(ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //; last by rewrite addnC Hrl. rewrite prednK //.
      have ueqr' : size ((access arrl (size arrl).-1) :: (delete arrr (i - size arrl))) < 2 * w ^ 2.
       rewrite /= size_delete //; last rewrite -(ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //; last by rewrite addnC Hrl. rewrite prednK //.
     rewrite -!addnBA //;last by apply leq_nth_count.
     rewrite count_delete -count_cat.
     rewrite subn1 [size arrr](size_delete1 (i - size arrl)) -[i - _ < _](ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //.
     rewrite addnC in Hrl. rewrite Hrl /= -subn1 -addnBA // subnn addn0.
     rewrite -size_cat -cat_last_belast // size_cat count_cat.
     by exists (Good Black (rnode (Leaf (delete arrl (size arrl).-1) leql (ltnW ueql)) (Leaf ((access arrl (size arrl).-1) :: (delete arrr (i - size arrl))) leqr' ueqr'))).
    rewrite leq_eqVlt bcr (size_delete1 (i - size arrl)) -[i - _ < _](ltn_add2r (size arrl)) subnK in leqr,ueqr;last rewrite leqNgt Hr //.
    rewrite addnC in Hrl. rewrite Hrl /= addn1 in leqr,ueqr.
    rewrite -!addnBA //;last exact: leq_nth_count.
    rewrite count_delete.
    rewrite subn1 [size arrr](size_delete1 (i - size arrl)) -[i - _ < _](ltn_add2r (size arrl)) subnK;last rewrite leqNgt Hr //.
    rewrite Hrl /= -subn1 -addnBA // subnn addn0.
    by exists (Good Black (rnode (Leaf arrl leql ueql) (Leaf (delete arrr (i - size arrl)) leqr (ltnW ueqr)))).
   rewrite nth_default;last first.
    rewrite -(leq_add2r (size arrl)) subnK; last by rewrite leqNgt Hr.
    by rewrite leqNgt addnC Hrl.
   rewrite /= !subn0.
   exists (Good Black (rnode (Leaf arrl leql ueql) (Leaf arrr leqr ueqr))).
   rewrite -delete_oversize //.
   rewrite -(leq_add2r (size arrl)) subnK; last by rewrite leqNgt Hr.
   by rewrite leqNgt addnC Hrl.
  Defined.

  Lemma ltn_subln a b c : a < b + c -> c > 0 -> a - b < c.
  Proof.
    case H : (b <= a). intros. by rewrite -(ltn_add2r b) subnK // addnC.
    move: H. rewrite leqNgt. move/negP/negP.
    case b => // n H.
    move/eqP: (ltnW H) => W.
    by rewrite W.
  Qed.

  Fixpoint ddelete {num ones d} (B : tree num ones d.+1 Black) i :
    { B' : near_tree' (num - (i < num)) (ones - (daccess B i)) d Black | dflattenn' B' = delete (dflatten B) i}.

    dependent inversion B as [|? ? ? ? ? cl cr ? ? ? l r seq oeq heq ceq] => //.
    move/eqP: heq l r. rewrite ceq /= eqSS. move/eqP => heq. rewrite heq => l r. rewrite delete_cat dflatten_sizeK.
    case: ifP => [Hl|Hr].
     clear heq c ceq B d0 num ones seq oeq.
     move: (sizeW' l) (sizeW' r) => GUARDL GUARDR.
     move: r.
     dependent inversion l as [arrl leql ueql sleq | ? ? ? ? ? cll clr ? cllok clrok ll lr seql oeql heql ceql] => r.
      rewrite -sleq in Hl.
      clear l. rewrite /=.
      dependent inversion r as [arrr leqr ueqr sreq | ? ? ? ? ? crl crr ? ? ? rl rr seqr oeqr heqr ceqr].
      case: (delete_leaves2 arrl arrr leql ueql leqr ueqr i).
      rewrite /= !delete_cat !nth_cat.
      case: ifP;last by rewrite Hl.
      move => ? res resK.
      rewrite -resK.
      by exists (Down res).
      destruct cr;last rewrite ceqr /= in heqr => //.
      destruct crl,crr => // /=.
      rewrite ceqr /= in heqr.
      move: rl rr.
      rewrite heqr => rl rr.
      move: (bzero_tree_is_leaf rl) (bzero_tree_is_leaf rr) => GUARD1 GUARD2.
      rewrite -sleq in GUARDL. rewrite -seqr in GUARDR.
      move: (sizeW' rl) (sizeW' rr) => GUARDRL GUARDRR.
      destruct rl as [arrrl leqrl ueqrl | ]; last first. by rewrite /= in GUARD1.
      destruct rr as [arrrr leqrr ueqrr | ]; last first. by rewrite /= in GUARD2.
      clear GUARD1 GUARD2.
      move: (delete_leaves3 arrl arrrl arrrr leql ueql leqrl ueqrl leqrr ueqrr i).
      rewrite -addnA  nth_cat.
      case: ifP => [? res|];last by rewrite Hl.
      by exists (Stay (Good Black (proj1_sig res)));
         rewrite /= (proj2_sig res) delete_cat;
         case: ifP;last by rewrite Hl.

      move: r cllok clrok.
      case cleq : cl;last first.
       case creq : cr.
        move => r cllok clrok.
        rewrite ceql cleq /= in heql. move: r. rewrite /= heql => r.
        dependent inversion r as [| ? ? ? ? ? crl crr ? crlok crrok rl rr seqr oeqr heqr ceqr].
        destruct crl,crr => //.
        set l' := (Node cllok clrok ll lr).
        rewrite ceqr /= in heqr. move: rl rr. rewrite heqr /= -heql => rl rr.
        case (ddelete _ _ _ (bnode (rnode l' rl) rr) i) => /=.
        case: ifP => [H1|];last by rewrite ltn_addr // seql.
        case: ifP => [H2|];last by rewrite seql Hl.
        rewrite !addnA => res resK.
        exists res; rewrite resK /= !delete_cat !size_cat !dflatten_sizeK.
        case: ifP;last by rewrite H1. case: ifP;last by rewrite H2.
        case: ifP; by rewrite !catA.
       move => r cllok clrok.
       case: (ddelete _ _ _ (bnode ll lr) i).
       rewrite /= delete_cat dflatten_sizeK.
       rewrite seql Hl.
       move => dl dlK.
       rewrite -dlK.
       rewrite ltn_addln // addsubnC // [_ + _ - _]addsubnC;last first.
        case: ifP => H.
         apply leq_addln; apply leq_access_count => //.
        apply leq_addrn; apply leq_access_count => //.
        rewrite -(ltn_add2r s0) subnK; last rewrite leqNgt H //.
        rewrite addnC seql //.
       clear l dlK.
       move: r dl => /=. set b := (if _ then _ else _). move => r dl.
       rewrite ceql /= in heql.
       destruct dl as [? ? ? dl|? ? ? dl].
        move: dl r. rewrite /= -cleq => dl r.
        destruct dl as [|? ? ? dlc' p dl'] => //.
        move: r. case peq : p. destruct p => //.
        move: dl'. case dlceq : dlc' => dl' r.
        case (balanceL Black (Good Black dl') r erefl erefl) => res resK.
        rewrite -resK.
        by exists (Stay res).
       by exists (Down (Good Black (rnode dl' r))).
       move: dl r. rewrite /= -cleq => dl r.
       destruct dl as [|? ? ? dlc' p dl'] => //.
       move: r. case peq : p. destruct p => //.
       move: dl'. case dlceq : dlc' => dl' r.
        set bracken := (black_of_red dl').
        exists (Down (Good Black (rnode (proj1_sig bracken) r))).
        by rewrite /= (proj2_sig bracken).
       destruct p => //. rewrite /= in heql. move: r. rewrite /= heql => r.
       destruct r as [| ? ? ? ? ? crl crr dc crlok crrok rl rr] => //.
        destruct dc => //.
        rewrite /= /dflatten.
        move/eqP in heql. rewrite /= eqSS in heql. move/eqP in heql.
        move: dl'. rewrite heql => dl'.
        move: rl. case crleq : crl.
         rewrite -crleq => rl.
         destruct rl as [|? ? ? ? ? crll crlr dc ? ? rll rlr] => //.
         destruct dc,crll,crlr => //.
         rewrite -!addnA [s + _]addnA [o + _]addnA.
         exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
         by rewrite /= !catA.
        move => rl.
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' rl) rr))).
        by rewrite /= !catA.
       move => r cllok clrok.
       rewrite /= delete_cat dflatten_sizeK.
       move: heql Hl GUARDL GUARDR ll lr r.
       rewrite ceql cleq /= => heql.
       rewrite heql -seql => Hl GUARDL GUARDR.
       case deq : d.
        case clleq : cll. by destruct cll.
        case clreq : clr. by destruct clr.
        move => ll lr r.
        move: (bzero_tree_is_leaf ll) (bzero_tree_is_leaf lr) => ? ?.
        destruct ll as [arrll leqll ueqll | ];last first. done.
        destruct lr as [arrlr leqlr ueqlr | ];last first. done.
        case: (delete_leaves2 arrll arrlr leqll ueqll leqlr ueqlr i).
        rewrite /= !delete_cat !nth_cat Hl.
        set b := (if _ then _ else _). move => dl dlK.
        rewrite -dlK [i < _ + _ ]ltn_addln //.
        rewrite [_ + _ - _]addsubnC // [_ + _ - b]addsubnC;last first.
         subst b; case :ifP => H. apply leq_addln; apply leq_nth_count. apply leq_addrn; apply leq_nth_count.
        clear dlK. move: dl. rewrite -clleq => dl.
        destruct dl as [|? ? ? ? dlc dll] => // /=.
        move: dll. rewrite clleq => dll.
        by exists (Stay (Good Black (bnode dll r))).
       move => ll lr r.
       case: ifP => [Hll|Hlr].
        destruct cll,clr => //.
        case (ddelete _ _ _ ll i).
        set b := (daccess _ _).
        rewrite Hll => dll dllK.
        rewrite ltn_addln //.
        rewrite -addnA -[_ + _ + _]addnA.
        rewrite [_ + _ - _]addsubnC;last by apply (sizeW' ll).
        rewrite [_ + _ - _]addsubnC;last subst b; last apply leq_access_count => //.
        rewrite -dllK.
        destruct dll as [? ? ? dll|? ? ? dll].
         clear dllK b ll l heql. move: lr r dll. rewrite /= -deq => lr r dll.
         rewrite !addnA.
         destruct dll as [|? ? ? dllc p dll] => //.
         destruct p => //.
         destruct dllc.
          set bad := (makeBadL dll lr).
          case (balanceL Black (` bad) r erefl erefl) => res resK.
          rewrite /= -(proj2_sig bad) -resK.
          by exists (Stay res).
         by exists (Stay (Good Black (bnode (rnode dll lr) r))).
        clear dllK b ll l heql. move: lr r dll. rewrite /= -deq => lr r dll.
        destruct dll as [? ? ? dll|? ? ? cdll tmp dll ] => //. destruct tmp => //.
        destruct cdll.
         set bracken := (black_of_red dll).
         move: lr r. rewrite deq => lr r.
         rewrite !addnA.
         exists (Stay (Good Black (bnode (rnode (proj1_sig bracken) lr) r))).
         by rewrite /= (proj2_sig bracken).
        destruct lr as [ ? |? ? ? ? ? clrl clrr crl' ? ? lrl lrr] => //.
        destruct clrl.
         destruct crl' => //.
         move/eqP in deq. rewrite /= eqSS in deq. move/eqP in deq.
         move: dll. rewrite -deq => dll.
         set bad := (makeBadR dll lrl).
         set fst := (balanceL Black (` bad) lrr erefl erefl).
         case (balanceL Black (` fst) r erefl erefl) => snd sndK.
         rewrite !addnA /= catA -(proj2_sig bad) -(proj2_sig fst) -sndK.
         by exists (Stay snd).
        destruct crl' => //.
        move/eqP in deq. rewrite /= eqSS in deq. move/eqP in deq.
        move: dll. rewrite -deq => dll.
        rewrite !addnA.
        exists (Stay (Good Black (bnode (bnode (rnode dll lrl) lrr) r))).
        by rewrite !catA.
       destruct cll,clr => //.
       rewrite ltnNge in Hlr.
       move/negP/negP in Hlr.
       case (ddelete _ _ _ lr (i - s0)).
       set b := (daccess _ _).
       rewrite ltn_addln //.
       rewrite ltn_subln //;last exact (sizeW' lr).
       move => dlr dlrK.
       rewrite [_ + _ - _]addsubnC //.
       rewrite -addnBA //;last exact (sizeW' lr).
       rewrite [_ + _ - b]addsubnC //;last first.
        apply leq_addrn. subst b; apply leq_access_count.
        rewrite ltn_subln //;last exact (sizeW' lr).
       rewrite -addnBA;last first.
        subst b ; apply leq_access_count.
        rewrite ltn_subln //;last exact (sizeW' lr).
       rewrite -dlrK.
       destruct dlr as [? ? ? dlr|? ? ? dlr].
        clear dlrK. move: ll r dlr. rewrite /= -deq => ll r dlr.
        destruct dlr as [|? ? ? dlrc p dlr] => //.
        destruct p => //.
        destruct dlrc.
         set bad := (makeBadR ll dlr).
         case (balanceL Black (` bad) r erefl erefl) => res resK.
         rewrite /= -(proj2_sig bad) -resK.
         by exists (Stay res).
        by exists (Stay (Good Black (bnode (rnode ll dlr) r))).
       clear dlrK. move: ll r dlr. rewrite /= -deq => ll r dlr.
       destruct dlr as [? ? ? dlr|? ? ? cdlr tmp dlr ] => //. destruct tmp => //.
       destruct cdlr.
        set bracken := (black_of_red dlr).
        move: ll r. rewrite deq => ll r.
        exists (Stay (Good Black (bnode (rnode ll (proj1_sig bracken)) r))).
        by rewrite /= (proj2_sig bracken).
       destruct ll as [ ? |? ? ? ? ? clll cllr cll' ? ? lll llr] => //.
       destruct cllr.
        destruct cll' => //.
        move/eqP in deq. rewrite /= eqSS in deq. move/eqP in deq.
        move: dlr. rewrite -deq => dlr.
        set bad := (makeBadL llr dlr).
        set fst := (balanceR Black lll (` bad) erefl erefl).
        case (balanceL Black (` fst) r erefl erefl) => snd sndK.
        rewrite /= -!catA [dflatten llr ++ _ ++ _]catA -(proj2_sig bad) catA -(proj2_sig fst) -sndK.
        rewrite -[s0 + _ + _]addnA -[o0 + _ + _]addnA.
        by exists (Stay snd).
       destruct cll' => //.
       move/eqP in deq. rewrite /= eqSS in deq. move/eqP in deq.
       move: dlr. rewrite -deq => dlr.
       rewrite -[s0 + _ + _]addnA -[o0 + _ + _]addnA.
       exists (Stay (Good Black (bnode (bnode lll (rnode llr dlr)) r))).
       by rewrite /= !catA.




       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.

      | BNode (RNode (ll,b,(BNode (lgl,d,lgg) as lg)),a,g) ->
         begin match bremove ll with
         | mll,Succ ll' -> (mll,Succ (BNode (RNode (ll',b,lg),a,g)))
         | mll,Red ll' -> (mll,Succ (BNode (RNode (black_of_red ll',b,lg),a,g)))
         | mll,Black ll' ->
            begin match lgl with
            | RNode _ -> (mll,Succ (BNode ((balanceLG (ll',b) d lgg lgl),a,g)))
            | BNode _ -> (mll,Succ (BNode (BNode (RNode (ll',b,lgl),d,lgg),a,g)))
            | Leaf -> (mll,Succ (BNode (BNode (RNode (ll',b,lgl),d,lgg),a,g)))
            end
         end

       destruct dll as [? ? ? dll|? ? ? dll].
        destruct cr.
         rewrite /= in heqr.
         move: rl rr. rewrite heqr => rl rr.
         destruct crl,crr => //.
         rewrite addnA.
         rewrite [o + (_ + _)]addnA.
         exists (Stay (bnode (rnode dll (bnode lrl lrr)) (rnode rl rr))).
         by rewrite /= -!catA.
        move/eqP in heqr.
        rewrite /= eqSS in heqr.
        move/eqP in heqr.
        move: rl rr. rewrite heqr => rl rr.
        rewrite addnA.
        rewrite [o + (_ + _)]addnA.
        exists (Stay (bnode (rnode dll (bnode lrl lrr)) (bnode rl rr))).
       destruct dll.


      | BNode (RNode (Leaf,b,Leaf),a,Leaf) -> (b,Succ (BNode (Leaf,a,Leaf)))

      | BNode (RNode (ll,b,(BNode (lgl,d,lgg) as lg)),a,g) ->
         begin match bremove ll with
         | mll,Succ ll' -> (mll,Succ (BNode (RNode (ll',b,lg),a,g)))
         | mll,Red ll' -> (mll,Succ (BNode (RNode (black_of_red ll',b,lg),a,g)))
         | mll,Black ll' ->
            begin match lgl with
            | RNode _ -> (mll,Succ (BNode ((balanceLG (ll',b) d lgg lgl),a,g)))
            | BNode _ -> (mll,Succ (BNode (BNode (RNode (ll',b,lgl),d,lgg),a,g)))
            | Leaf -> (mll,Succ (BNode (BNode (RNode (ll',b,lgl),d,lgg),a,g)))
            end
         end
        
        ;last by apply (sizeW' ll).
        apply sizeW'.
        // [_ + _ - b]addsubnC;last first.

        apply leq_addln;subst b.
        ;apply leq_access_count => //.
        
          case :ifP => H. apply leq_addln; apply leq_nth_count. apply leq_addrn; apply leq_nth_count.
        

        rewrite /= !delete_cat !nth_cat.
        case: ifP;last by rewrite Hll.
       move => /= ? dl dlK.
       rewrite -dlK [i < _ + _ ]ltn_addln;last by apply ltn_addln => //.
       clear dlK.
       move: dl.
       rewrite [i < _ + _ ]ltn_addln //.
       rewrite [_ + (_  + _) - _]addsubnC;last apply ltn_addln; last apply sizeW => //.
       rewrite [_ + (_  + _) - _]addsubnC ;last apply leq_addln ; last apply leq_nth_count => //.
       rewrite !subn1 => dl.
       destruct dlc => //.
        
        case (balanceL Black dl r erefl erefl) => res resK.
        exists (Stay res).
        rewrite addsubnC.
        rewrite -addnBA.

        move => r dl.
        set b := 
        ;last first.

apply ltn_addln .
        clear dlK.
        move: dl.

        rewrite [i < _ + _ ]ltn_addln //. => dl.
        
        ;last apply ltn_addln; last apply sizeW => //.
       rewrite [_ + (_  + _) - _]addsubnC ;last apply leq_addln ; last apply leq_nth_count => //.
       rewrite !subn1 => dl.
       destruct dl as [|? ? ? ? dlc dll] => // /=.
       destruct dlc => //.
       by exists (Stay (bnode dll (rnode rl rr))).


      destruct cll,clr => //.
      destruct lr as [arrlr leqlr ueqlr ? |? ? ? ? ? clrl clrr clr' ? ? lrl lrr].
       rewrite ceqr -heql /= in heqr. 
       destruct cr,crl,crr => //.
       move: rl rr. rewrite /= in heqr. rewrite /= heqr => rl rr.
       move: (bzero_tree_is_leaf ll) (bzero_tree_is_leaf rl) (bzero_tree_is_leaf rr) => GUARD1 GUARD2 GUARD3.
       destruct ll as [arrll leqll ueqll | ]; last first. by rewrite /= in GUARD1.
       case: (delete_leaves2 arrll arrlr leqll ueqll leqlr ueqlr i).
       rewrite /= !delete_cat !nth_cat.
       case: ifP;last by rewrite Hll.
        

          by destruct cll.
        rewrite -clleq -deq => ll.
        clear l.
        move: arrll Hl GUARDL GUARDR oeql ceql seql leqll ueqll .
        rewrite -clreq -heql. => lr.
         
        rewrite -deq => ll lr r.

       => ll lr r.
        
       ll lr r.
       move: ll lr r.
       rewrite heql


       
        move: dl'. rewrite heql => dl'.
        
        inversion rl as [|? ? ? ? ? crll crlr ?  ? ? rll rlr seqrl oeqrl heqrl ceqrl].
         by rewrite ceqrl /= in heqrl.
         destruct rl.
        rewrite -seqrl.
         rewrite ceqrl /= in heqrl. move: rll rr. rewrite heqr => rl rr.
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).

        rewrite ceqrl /= in heqrl.
        move: rll rr. rewrite heqr => rl rr.
        Check (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
       rewrite /dflattenn' /= /dflattenn /dflatten .
       clear b ll lr heql seql ceql oeql cllok clrok GUARDL GUARDR i0 i1 cll clr c d Hl.
       dependent inversion r as [| ? ? ? ? ? crl crr ? crlok crrok rl rr seqr oeqr heqr ceqr].
       rewrite /= -/(dflattenn' _).
       move: dl' => /=.
       rewrite ceqr /= in heqr. move/eqP in heqr. rewrite eqSS in heqr. move/eqP in heqr.
       move: rl rr. rewrite heqr => rl rr.
        destruct crl.
        inversion rl as [|? ? ? ? ? crll crlr ?  ? ? rll rlr seqrl oeqrl heqrl ceqrl].
        rewrite ceqrl /= in heqrl.
        move: rll rr. rewrite heqr => rl rr.
        Check (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        inversion r as [| ? ? ? ? ? crl crr ? crlok crrok rl rr seqr oeqr heqr ceqr].
        rewrite -seqr.
         

            | RNode _ -> (ml,Red (balanceLG (l',a) c gg gl))
            | BNode _ -> (ml,Black (BNode (RNode (l',a,gl),c,gg)))
        Check (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
       rewrite /=.
       dependent inversion r as [| ? ? ? ? ? crl crr ? crlok crrok rl rr seqr oeqr heqr ceqr].
       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.
       
       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.
       
       destruct dl as [|? ? ? dlc' ? dl'].
       dependent inversion dl as [|? ? ? dlc' ? dl'].
       dependent inversion dl as [s o ? dl|? ? ? dl].
       rewrite /= in heql.
        move: dl. rewrite /= heql -heqr => dl.
        by exists (Down (Good Black (rnode dl (bnode rl rr)))).

       case: ifP;last by rewrite Hll.
       rewrite -dlK.
       clear l dlK.
       rewrite [o0 + o3 + _ - _]addsubnC;last apply: leq_addln;last apply: leq_access_count => //.

       rewrite -heqr in heql. move/eqP in heql. rewrite eqSS in heql. move/eqP in heql.
       move: dl rl rr. rewrite /= heql => dl.
       dependent inversion dl as [|? ? ? dlc' ? dl'] => rl rr.
        destruct dlc'.
        set bracken := (black_of_red dl').
        exists (Down (Good Black (rnode (proj1_sig bracken) (bnode rl rr)))).
        by rewrite /= (proj2_sig bracken).
       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.
        
       
      | BNode ((BNode _ as l),a,RNode (gl,b,gg)) -> bremove (BNode (RNode(l,a,gl),b,gg))
       rewrite -deq /= in heql.
       destruct cl,cll,clr => //.
       rewrite /= in heql.
       move: ll lr.
       rewrite heql => ll lr.
       move: (bzero_tree_is_leaf ll) (bzero_tree_is_leaf lr) => GUARD1 GUARD2.
       destruct ll as [arrll leqll ueqll | ]; last first. by rewrite /= in GUARD1.
       destruct lr as [arrlr leqlr ueqlr | ]; last first. by rewrite /= in GUARD2.
       clear GUARD1 GUARD2.
       move: (delete_leaves3 arrll arrlr arrr leqll ueqll leqlr ueqlr leqr ueqr i).
       rewrite -seql in Hl.
       rewrite nth_cat !addnA /=.
       case: ifP => [Hll res|].
        exists (Stay (proj1_sig res)).
        by rewrite /= (proj2_sig res) !delete_cat;case: ifP;rewrite catA;rewrite Hll.
       rewrite nth_cat.
       case: ifP => [Hlr Hll res|nHl Hll];last first. move: nHl;rewrite -(ltn_add2r (size arrll)) subnK;last rewrite leqNgt Hll //;rewrite addnC Hl //.
       exists (Stay (proj1_sig res)).
       by rewrite /= (proj2_sig res) !delete_cat; case: ifP;rewrite catA //;case: ifP;rewrite catA //; rewrite Hlr.
      rewrite delete_cat dflatten_sizeK.

     case: ifP => [Hll|Hlr].
      destruct cl;last first.
       destruct cr.
        destruct crl,crr => //.
        rewrite ceqr /= in heqr. move: rl rr. rewrite heqr -heql /= => rl rr.
        move: (ddelete _ _ _ (bnode (rnode (bnode ll lr) rl) rr) i) => /=.
        case: ifP => [H1|];last by rewrite ltn_addr // seql. case: ifP => [H2|];last by rewrite ltn_addr //. case: ifP => [H3|];last by rewrite Hll.
        rewrite !addnA => res.
        exists (proj1_sig res); rewrite (proj2_sig res) /= !delete_cat !size_cat !dflatten_sizeK.
        case: ifP;last by rewrite H1. case: ifP;last by rewrite H2. case: ifP;last by rewrite H3.
        by rewrite !catA.

       rewrite ceqr /= in heqr. rewrite /= heqr -heql.
       case: (ddelete _ _ _ (bnode ll lr) i).
       rewrite /= delete_cat dflatten_sizeK.
       case: ifP;last by rewrite Hll.
       rewrite ltn_addln // ltn_addln //;last apply ltn_addln => //.
       move => ? dl dlK.
       rewrite -dlK.
       clear l dlK.
       rewrite addsubnC;last by rewrite seql GUARDL.
       rewrite [o0 + o3 + _ - _]addsubnC;last apply: leq_addln;last apply: leq_access_count => //.
       rewrite /= in heql.
       destruct dl as [s o ? dl|? ? ? dl].
        move: dl. rewrite /= heql -heqr => dl.
        by exists (Down (Good Black (rnode dl (bnode rl rr)))).
       rewrite -heqr in heql. move/eqP in heql. rewrite eqSS in heql. move/eqP in heql.
       move: dl rl rr. rewrite /= heql => dl.
       dependent inversion dl as [|? ? ? dlc' ? dl'] => rl rr.
        destruct dlc'.
        set bracken := (black_of_red dl').
        exists (Down (Good Black (rnode (proj1_sig bracken) (bnode rl rr)))).
        by rewrite /= (proj2_sig bracken).
       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.

      destruct cll,clr => //.
      destruct lr as [arrlr leqlr ueqlr ? |? ? ? ? ? clrl clrr clr' ? ? lrl lrr].
       rewrite ceqr -heql /= in heqr. 
       destruct cr,crl,crr => //.
       move: rl rr. rewrite /= in heqr. rewrite /= heqr => rl rr.
       move: (bzero_tree_is_leaf ll) (bzero_tree_is_leaf rl) (bzero_tree_is_leaf rr) => GUARD1 GUARD2 GUARD3.
       destruct ll as [arrll leqll ueqll | ]; last first. by rewrite /= in GUARD1.
       case: (delete_leaves2 arrll arrlr leqll ueqll leqlr ueqlr i).
       rewrite /= !delete_cat !nth_cat.
       case: ifP;last by rewrite Hll.
       move => /= ? dl dlK.
       rewrite -dlK [i < _ + _ ]ltn_addln;last by apply ltn_addln => //.
       clear dlK.
       move: dl.
       rewrite [i < _ + _ ]ltn_addln //.
       rewrite [_ + (_  + _) - _]addsubnC;last apply ltn_addln; last apply sizeW => //.
       rewrite [_ + (_  + _) - _]addsubnC ;last apply leq_addln ; last apply leq_nth_count => //.
       rewrite !subn1 => dl.
       destruct dl as [|? ? ? ? dlc dll] => // /=.
       destruct dlc => //.
       by exists (Stay (bnode dll (rnode rl rr))).
      destruct clr' => //.
      rewrite ceqr -heql in heqr.
      move: ll Hll. rewrite /inc_black => ll Hll.
      rewrite [i < _ + _ ]ltn_addln;last by apply ltn_addln => //.
      rewrite -addnA addsubnC;last by exact : (sizeW' ll).
      rewrite -[o0 + _ + _]addnA addsubnC;last by exact : leq_access_count.
      case (ddelete _ _ _ ll i).
      case (daccess ll i);last first. (* workaround *)
       rewrite /= in heql,heqr.
       rewrite Hll !subn1 !subn0 => dll dllK.
       rewrite -dllK -!catA /dflattenn' /=.
       clear dllK.
       destruct dll as [? ? ? dll|? ? ? dll].
        destruct cr.
         rewrite /= in heqr.
         move: rl rr. rewrite heqr => rl rr.
         destruct crl,crr => //.
         rewrite addnA.
         rewrite [o + (_ + _)]addnA.
         exists (Stay (bnode (rnode dll (bnode lrl lrr)) (rnode rl rr))).
         by rewrite /= -!catA.
        move/eqP in heqr.
        rewrite /= eqSS in heqr.
        move/eqP in heqr.
        move: rl rr. rewrite heqr => rl rr.
        rewrite addnA.
        rewrite [o + (_ + _)]addnA.
        exists (Stay (bnode (rnode dll (bnode lrl lrr)) (bnode rl rr))).
        by rewrite /= -!catA.
       destruct dll as [? ? ? dll|? ? ? cdll p dll] => //.
       destruct p => //.
        destruct cr.
         destruct crl,crr => //.

       rewrite /= in heql,heqr.
       rewrite Hll !subn1 => dll dllK.
       rewrite -dllK -!catA /dflattenn' /=.
       clear dllK.
       destruct dll as [? ? ? dll|? ? ? dll].
       destruct cr.
        rewrite /= in heqr.
        move: rl rr. rewrite heqr => rl rr.
        destruct crl,crr => //.
        rewrite addnA.
        rewrite [o + (_ + _)]addnA.
        exists (Stay (bnode (rnode dll (bnode lrl lrr)) (rnode rl rr))).
        by rewrite /= -!catA.
       move/eqP in heqr.
       rewrite /= eqSS in heqr.
       move/eqP in heqr.
       move: rl rr. rewrite heqr => rl rr.
       rewrite addnA.
       rewrite [o + (_ + _)]addnA.
       exists (Stay (bnode (rnode dll (bnode lrl lrr)) (bnode rl rr))).
       by rewrite /= -!catA.
      rewrite /= in heql,heqr.
      rewrite Hll. !subn1 !addn0 => dll dllK.
      rewrite -dllK -!catA /dflattenn' /=.
      clear dllK.
      destruct dll as [? ? ? dll|? ? ? dll].
      destruct cr.
       rewrite /= in heqr.
       move: rl rr. rewrite heqr => rl rr.
       destruct crl,crr => //.
       rewrite addnA.
       rewrite [o + (_ + _)]addnA.
       exists (Stay (bnode (rnode dll (bnode lrl lrr)) (rnode rl rr))).
       by rewrite /= -!catA.
      move/eqP in heqr.
      rewrite /= eqSS in heqr.
      move/eqP in heqr.
      move: rl rr. rewrite heqr => rl rr.
      rewrite addnA.
      rewrite [o + (_ + _)]addnA.
      exists (Stay (bnode (rnode dll (bnode lrl lrr)) (bnode rl rr))).
      by rewrite /= -!catA.

      rewrite heqr. in r'.
      set r' := (Node crlok crrok rl rr).
      rewrite /= in heqr.
      move : r. rewrite -heql => r.
      destruct dll.
      rewrite [((dflatten lrl ++ _) ++ _) ++ _]catA.
      destruct cr.
       destruct crl,crr => //.
       move: ll dll heqr lrl lrr rl rr => ll dll /= heqr. rewrite heqr => lrl lrr rl rr.

       destruct dll.

      rewrite /= heql in heqr.
      move: rl rr => /=.
      rewrite heqr.
      rewrite heql ll rl rr dll.

       ;last by rewrite seql.
       ;last by rewrite seql.
       rewrite addsubnC;last by rewrite seql.
       rewrite [count_one arrlr + _ - _]addnA.
       rewrite -addnBA.
       ;last by rewrite seql.
       rewrite -addnBA.
       rewrite -addnA.

       => res resK.

       intros.


      by exists (Down res).

       destruct rl as [arrrl leqrl ueqrl | ]; last first. by rewrite /= in GUARD2.
       destruct rr as [arrrr leqrr ueqrr | ]; last first. by rewrite /= in GUARD3.

       case bcll : (w ^ 2 %/ 2 == size arrll).
        case bcr : (w ^ 2 %/ 2 == size arrr).
         move/eqP in bcl. move/eqP in bcr.
         rewrite -sleq in GUARDL. rewrite -sreq in GUARDR.
         have ueq : size ((rcons (delete arrl i) (access arrr 0)) ++ (delete arrr 0)) < 2 * w ^ 2.
          move/eqP: wordsize_sqrn_div2_neq0. rewrite -lt0n => GUARD1.
          move: (ltn_addrn 0 (w ^ 2 %/ 2) _ GUARD1) => GUARD2.
          rewrite size_cat size_rcons !size_delete // -bcl -bcr -subn1 -2!addn1 subnK // addnBA // subnK //.
          exact: (ltnW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
         have leq : size (rcons (delete arrl i) (access arrr 0) ++ delete arrr 0) >= w ^ 2 %/ 2.
          rewrite size_cat size_rcons !size_delete // -[_.-1]subn1 -[(_ - 1).+1]addn1 subnK //.
          exact: leq_addln => //.
         rewrite ltn_addln => //.
         rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat addsubnC;last exact: leq_nth_count.
         rewrite count_delete -count_cat -cat_head_behead //.
         by exists (Down (Good Black (Leaf ((rcons (delete arrl i) (access arrr 0)) ++ (delete arrr 0)) leq ueq))).
        rewrite -sleq in GUARDL. rewrite -sreq in GUARDR.
        rewrite /=.
        rewrite leq_eqVlt bcr (size_delete1 0) GUARDR /= addn1 in leqr,ueqr.
        rewrite -(size_rcons_delete i (access arrr 0)) // in leql,ueql.
        rewrite ltn_addln => //.
        rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat addsubnC;last exact: leq_nth_count.
        rewrite count_delete -count_cat -cat_head_behead // count_cat size_cat.
        by exists (Stay (Good Black (bnode (Leaf (rcons (delete arrl i) (access arrr 0)) leql ueql) (Leaf (delete arrr 0) leqr (ltnW ueqr))))).
       rewrite -sleq in GUARDL. rewrite -sreq in GUARDR.
       rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
       rewrite ltn_addln => //.
       rewrite addnC -addnBA // subn1 -(size_delete Hl) /= addnC addsubnC;last exact: leq_nth_count.
       rewrite count_delete.
       by exists (Stay (Good Black (bnode (Leaf (delete arrl i) leql (ltnW ueql)) (Leaf arrr leqr ueqr)))).
       
       rewrite /= !delete_cat !nth_cat. 
       case:ifP;last by rewrite Hll.
       rewrite ltn_addln; last apply ltn_addln => //.
       rewrite ltn_addln;last rewrite ltn_addln => //.
       rewrite /= !subn1 => ? dl dlK.
       rewrite -subn1 addnA addsubnC; last apply ltn_addln; last rewrite seql => //.
       rewrite -addnA subn1.
       rewrite [count_one _ + _ + _]addnA addsubnC; last apply leq_addln; last apply leq_addln; last apply leq_nth_count.
       rewrite -[count_one _ + _ + _]addnA.
       rewrite catA -[(delete _ _ ++ _ ) ++ _]catA -dlK.
       
       rewrite catA -catA.
       rewrite -catA {2}catA.
         last rewrite seql => //.
       ht
       . ;last exact: (sizeW _ leqll).
       rewrite addsubnC //.
       rewrite subn1. -catA -dlK.
       dependent inversion dl as [? ? ? dl'|? ? ? dl'].
       clear dlK dl.
        rewrite /=.
        dependent inversion dl' as [|? ? ddl'' cdl'' cdl' dl''] => //.

       case: (ddelete _ _ _ (bnode (Leaf arrll leqll ueqll) (Leaf arrlr leqlr ueqlr)) i).

        rewrite !/dflattenn' /dflattenn.

        destruct dl' => //.
        destruct cdl' => //.
        destruct dl'' as [|? ? ? ? ? cdll cdlr cdl ? ? dll dlr seqdl oeqdl heqdl ceqdl].
        destruct cdl.
        rewrite /= in heqdl. move: dll dlr. rewrite heqdl => dll dlr.
        destruct cdl'',cdll,cdlr => //.
        Check (balanceL Black (Good Red (rnode dll dlr)) (bnode (Leaf arrrl leqrl ueqrl) (Leaf arrrr leqrr ueqrr)) erefl erefl).
        inversion dlr as [|? ? ? ? ? cdlrl cdlrr cdlr' ? ? dlrl dlrr seqdlr oeqdlr heqdlr ceqdlr].
        move/eqP: heqdlr dlrl dlrr. rewrite ceqdlr /= eqSS. move/eqP => heqdlr. rewrite heqdlr => dlrl dlrr.
        Check (Stay (Bad dll dlr 
       Check (balanceL Black dl'  erefl erefl).
         i).
       case: (ddelete _ _ _ 
        clear dl.
        rewrite /= in heql.
         (bnode dll
                dlrl
           (bnode dlrr (Leaf arrrr))
           dlrr 

       rewrite !addnA -[size _ + size _ + _]addnA 
       rewrite -dlK /= !subn1 -2!addnA. [size arrll + (_ + _)]addnA 
       rewrite -[count_one _ + count_one _ + _]addnA.
       move: dl. rewrite addnA subn1 => dl.
       rewrite !subn1 /= => ? dl dlK.
       rewrite -dlK.

       rewrite ltn_addln => //.
       ;last rewrite ltn_addln => //.

       => /= lh lhK.
                arrll arrlr arrrl leqrl ueqrl i).
       case: (delete_leaves3 arrll arrlr arrrl leqll ueqll leqlr ueqlr leqrl ueqrl i).
       rewrite /= catA -[(delete arrll i ++ arrlr) ++ arrrl]catA -dlK.
       clear dlK.
        clear r.
        rewrite /=.

         destruct dl' as [arrdl leqdl ueqdl | ].
        clear GUARD1 GUARD2 GUARD3 dl.
        destruct dl' => //.
        move: arrll arrlr leqll ueqll leqlr ueqlr seql heql ceql oeql dl' H H0 H1 Hll.
        destruct dl'.

       rewrite seql. GUARDL.
       case dleq :dl.
       move: (heql) => ?.
       rewrite /= in heql.

        inversion dl'.
       rewrite /= in heql.
                rewrite -dlK.
       rewrite /= -dlK addsubnC;last by rewrite seql GUARDL.
       rewrite [_ + count_one _ + _ - _]addsubnC;last by apply: leq_addln leq_nth_count.
       clear dlK.
       rewrite /=.
       dependent inversion dl.

       case dl.
       destruct dl.
       move: ll arrlr leqlr ueqlr seql oeql ceql heql rl rr.
       destruct dl as [s o ? dl|? ? ? dl].

      

 (bnode rl rr)

      rewrite -addnA (ltn_addr _ Hl) nth_cat.
      case: ifP => [? res|];last by rewrite Hl.
      by exists (proj1_sig res);
         rewrite (proj2_sig res) /= delete_cat;
         case: ifP;last by rewrite Hl.

       rewrite ceqr -heql /= in h#heqr.
      destruct cr.
      move: (ddelete _ _ _ ll i).


       rewrite ceqr /= in heqr. move: rl rr. rewrite heqr -heql /= => rl rr.
       case: ifP => [H1|];last by rewrite ltn_addr // seql. case: ifP => [H2|];last by rewrite ltn_addr //. case: ifP => [H3|];last by rewrite Hll.
       rewrite !addnA => res.
       exists (proj1_sig res); rewrite (proj2_sig res) /= !delete_cat !size_cat !dflatten_sizeK.
       case: ifP;last by rewrite H1. case: ifP;last by rewrite H2. case: ifP;last by rewrite H3.
       by rewrite !catA.

       rewrite ceqr /= in heqr.
       rewrite /= heqr -heql.
       case: (ddelete _ _ _ (bnode ll lr) i).
       rewrite /= delete_cat dflatten_sizeK.
       case: ifP;last by rewrite Hll.
       move => ? dl dlK.
       rewrite -dlK.
       clear l dlK.
       rewrite addsubnC;last by rewrite seql GUARDL.
       rewrite [o0 + o3 + _ - _]addsubnC;last exact: (leq_addln _ _ o3 (leq_access_count ll i Hll)).
       rewrite /= in heql.
       destruct dl as [s o ? dl|? ? ? dl].
        move: dl.
        rewrite /= heql -heqr => dl.
        case: (balanceL Black dl (bnode rl rr) erefl erefl) => /= res resK.
        exists (Stay res).
        by rewrite -resK.
       rewrite -heqr in heql. move/eqP in heql. rewrite eqSS in heql. move/eqP in heql.
       move: dl rl rr. rewrite /= heql => dl.
       dependent inversion dl as [|? ? ? dlc' ? dl'] => rl rr.
        destruct dlc'.
        set bracken := (black_of_red dl').
        exists (Down (Good Black (rnode (proj1_sig bracken) (bnode rl rr)))).
        by rewrite /= (proj2_sig bracken).
       destruct rl as [arrrl leqrl ueqrl ? |? ? ? ? ? crll crlr crl' ? ? rll rlr].
        rewrite !addnA.
        exists (Down (Good Black (bnode (rnode dl' (Leaf arrrl leqrl ueqrl)) rr))).
        by rewrite /= catA.
       destruct crl'.
        destruct crll,crlr => //.
        rewrite -!addnA [s + _]addnA [o + _]addnA.
        exists (Down (Good Black (rnode (bnode dl' rll) (bnode rlr rr)))).
        by rewrite /= !catA.
       rewrite [s + _]addnA [o + _]addnA.
       exists (Down (Good Black (bnode (rnode dl' (bnode rll rlr)) rr))).
       by rewrite /= -!catA.
      
      | BNode (Leaf,v,Leaf) -> (v,Black Leaf)
      | BNode (Leaf,a,RNode (Leaf,c,Leaf)) -> (a,Succ (BNode (Leaf,c,Leaf)))
      | BNode (RNode (Leaf,b,Leaf),a,Leaf) -> (b,Succ (BNode (Leaf,a,Leaf)))
      | BNode (RNode (Leaf,b,Leaf),a,RNode (Leaf,c,Leaf)) -> (b,Succ (BNode (Leaf,a,RNode (Leaf,c,Leaf))))
      | BNode ((BNode _ as l),a,(BNode (gl,c,gg) as g)) -> 
         begin match bremove l with
         | ml,Succ l' -> (ml,Succ (BNode (l',a,g)))
         | ml,Red l' -> (ml,Red (RNode (black_of_red l',a,g)))
         | ml,Black l' ->
            begin match gl with
            | RNode _ -> (ml,Red (balanceLG (l',a) c gg gl))
            | BNode _ -> (ml,Black (BNode (RNode (l',a,gl),c,gg)))
            | Leaf -> (ml,Black (BNode (RNode (l',a,gl),c,gg)))
            end
         end

        exists (Down (Good Black (rnode
                                    dl' (bnode rl rr)))).
        About black_of_red.
        
         rewrite -heqr in heql. move/eqP in heql. rewrite eqSS /= in heql. move/eqP in heql.
         move: dl rr rll rlr. rewrite /= heql => dl rr rll rlr.

         case: (balanceL Black (Bad dl rll rlr) rr erefl erefl) => /= res resK.

         Check (Down res).
         rewrite /= in heqr.

         rewrite heql -heqr.
        

        rewrite -heql heqr.
          in dl.
        move: rl rr.
        rewrite /= in heql.
        rewrite {1}heql -heqr => rl rr.

        hhhhjj
         



        daccess_leq
        apply : leq_addr.
        case dl.
        case dlc : dl.
        move: dl.h
        case.#hjj
        rewrite -heql.
        case.
        case dlc : dl.
       
          !delete_cat;case: ifP;rewrite catA;rewrite Hll.

       destruct cll,clr => //.
       hhhhhhhhhhh
      move/negP/negP.
      move/negPn.
      move/eqP.
      move/eqP in Hl.

       apply/eqP.
       rewrite !catA.

       rewrite drop_oversize.
       rewrite catA //;
      rewrite !catA //.
      intros.

      rewrite -sleq in GUARDL. rewrite -seqr in GUARDR.
      move: (sizeW' rl) (sizeW' rr) => GUARDRL GUARDRR.

     have H6 : size (rcons (delete arr i5) (access arr0 0)) = size arr. rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
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

          move: (leq_size_catr _ (delete arrr 0) arrl Hl).
    -subn1. -subSn. addnK. -addn1. subnK. -addn1. -subn1. subSS. -bcl -bcr -subn1. subnK. // addnBA // subnK //.
         rewrite {1}bcl {1}bcr in ueq.

    move: B i oki.
    case d => [B i oki|].
      rewrite /dflatten.
      move: B r.
      dependent inversion l.
       as [|? ? ? ? ? cl cr ? ? ? l r seq oeq heq ceq] => //.
      

     move: l r.
    move/eqP in heq.
    rewrite in heq.
    move/eqP in heq.
    rewrite heq in l,r.
    dependent inversion d.

    move: B i oki.

    case H : d => B.
    move: (pos_tree_is_not_leaf B) => GUARD1.
    destruct B => //.
    generalize d.
    elim => [B i oki|].



    move/eqP: wordsize_sqrn_div2_neq0. rewrite -lt0n => GUARD1.
    move: (ltn_addrn 0 (w ^ 2 %/ 2) _ GUARD1) => GUARD2.
    rewrite /is_leaf in GUARD3.
    rewrite daccessK /delete !/dflatten.
      /daccess delete_cat dflatten_sizeK.

    rewrite addsubnC;last exact: 
    case: ifP => H.
     case_eq (s1 == (w ^ 2) %/ 2) => H2.
     (* B1 = Leaf, B2 = Leaf or (Red Leaf Leaf)*)
     destruct B1;last first.
     dependent destruction B1.
      move/implyP: (size_of_node (Node i2 i3 B1_1 B1_2)) => /=.
      move/eqP: H2 => H2.
      rewrite H2 => H3.
      move: (technical1 (w ^ 2 %/ 2) H3) => H4.
      move/eqP: wordsize_sqrn_div2_neq0.
      by rewrite H4 /=.
     dependent induction B2;last first.
      destruct c0;last first. move: (technical2 d0). rewrite /= in x0. by rewrite /= x0.
      destruct c => //.
      dependent induction B2_1;last first.
       destruct c => //. move: (technical2 d0). rewrite /= in x0. by rewrite /= x0.
      dependent induction B2_2;last first.
       destruct c => //. move: (technical2 d0). rewrite /= in x0. by rewrite /= x0.
      rewrite -x /=.
      move: (sizeW arr i2) (sizeW arr0 i5) (sizeW arr1 i7) => ? H7 H8.
      clear IHB2_1 IHB2_2 GUARD5.
      rewrite -(size_rcons_delete i9 (access arr0 0)) // in i2,i3.
      case_eq (w ^ 2 %/ 2 == size arr0).
       move/eqP => H4.
       case_eq (w ^ 2 %/ 2 == size arr1).
        move/eqP => H5.
        have i11 : size ((delete arr0 0) ++ arr1) < 2 * w ^ 2.
         rewrite size_cat size_delete // -H4 -H5 addnC -subn1 !addnBA // -(ltn_add2r 1) subnK // addn1.
         exact : (leqW (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0)).
        rewrite [size _ + _ - _]addsubnC //.
        rewrite [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
        rewrite count_delete /count_one -!count_cat catA
                (size_delete1 i9) H /= -addnBA // subnn addn0 -!size_cat catA
               -(cat_delete_behead arr arr0 H7) -catA count_cat size_cat.
        (* さがって あがる *)
        by exists (Stay (Good Black (bnode (Leaf (rcons (delete arr i9) (access arr0 0)) i2 i3) (Leaf ((delete arr0 0) ++ arr1) (leq_size_catr _ (delete arr0 0) arr1 i7) i11)))).
       clear x => H5.
       rewrite leq_eqVlt H5 (size_delete1 0) H8 /= addn1 in i7.
       move : (ltnW i8) => i8'.
       rewrite (size_delete1 0) H8 /= addn1 /= in i8'.
       have i10 : w ^ 2 %/ 2 <= size ((delete arr i9) ++ (rcons arr0 (access arr1 0))). rewrite size_cat size_rcons leq_addrn //;last exact: (leqW i5).
       have i11 : 2 * w ^ 2  > size ((delete arr i9) ++ (rcons arr0 (access arr1 0))).
        move/eqP: H2 => H2.
        rewrite size_cat size_rcons size_delete // H2 -H4 addnC -subn1 // -2!addn1 -addnA subnK // addnC addnA addn1.
        exact: (leq_divn2n_mul2 (w ^ 2) wordsize_sqrn_gt0).
       rewrite [size _ + _ - _]addsubnC // [count_one _ + _ - _]addsubnC;last exact: leq_nth_count.
       rewrite count_delete /count_one -!count_cat catA (size_delete1 i9) H /= -addnBA // subnn addn0 -!size_cat -(cons_head_behead arr1) //
               -delete0_behead -cat_rcons catA size_cat -catA -cat_rcons catA count_cat.
       exists (Stay (Good Black (bnode (Leaf ((delete arr i9) ++ (rcons arr0 (access arr1 0))) i10 i11) (Leaf (delete arr1 0) i7 i8')))).
       by rewrite /= -/(nth false _ 0) -/(access _ _) catA take0 drop1 cats0 -catA.
      clear x => H4.
      rewrite leq_eqVlt H4 (size_delete1 0) H7 /= addn1 in i5.
      rewrite (size_delete1 0) H7 /= addn1 in i6.
      rewrite /count_one -!count_cat catA -(size_rcons_delete i9 (access arr0 0)) // addnA addnC addnA -addnBA // subn1 -(size_delete H7) -addnA addnC -addnA
              !count_cat [(count_mem _) _ + _]addnC addsubnC;last apply: leq_addrn leq_nth_count.
      rewrite -addnBA -/(count_one arr);last exact: leq_nth_count.
      rewrite count_delete [(count_mem _) _ + _]addnC -count_cat -(cat_delete_behead arr arr0 _) // count_cat -addnA.
      exists (Stay (Good Black (bnode (Leaf (rcons (delete arr i9) (access arr0 0)) i2 i3)
                          (rnode (Leaf (delete arr0 0) i5 (ltnW i6)) (Leaf arr1 i7 i8))))).
      by rewrite /= -/(nth false _ 0) -/(access _ _) catA cat_delete_behead // -catA.
     (* B2 = Leaf *)
     move: (sizeW arr i2) (sizeW arr0 i1) => H4 H5.
     case_eq (w ^ 2 %/ 2 == size arr0) => H3.
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
     destruct c.
      by exists (Stay (Good Red (Leaf ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0)) i10 i11))).
     by exists (Down (Leaf ((rcons (delete arr i5) (access arr0 0)) ++ (delete arr0 0)) i10 i11)).
    move: (i1) (i4) (i2) (i3) => ? ? ? ?.
    clear IHB1 IHB2 okB.
    rewrite -(size_rcons_delete i5 (access arr0 0)) // in i2,i3.
    rewrite leq_eqVlt H3 (size_delete1 0) H5 /= addn1 in i1,i4.
    rewrite -addnBA // subn1 -(size_delete H5) /= addsubnC;last exact: leq_nth_count.
    rewrite -(size_rcons_delete i5 (access arr0 0)) // count_delete -count_cat -(cat_delete_behead arr arr0 _) // count_cat.
    exists (Stay (Good c (Node i0 i (Leaf (rcons (delete arr i5) (access arr0 0)) i2 i3) (Leaf (delete arr0 0) i1 (ltnW i4))))).
    by rewrite /= catA.
    
   have okB1 : (wordsize_ok B1).
    destruct B1 => // /=. clear okB.
    move: (i2) => i2'. rewrite leq_eqVlt eq_sym H2 /= in i2'. apply/andP. split => //. exact: (ltnW i3).
   case (IHB1 i1 okB1 H GUARD2 GUARD1 GUARD3) => dB1 dB1K.
   clear IHB1 IHB2 okB.
   dependent induction dB1.
    rewrite addsubnC;last exact: (sizeW' B1).
    rewrite addsubnC;last first.
     rewrite -/(daccess _) daccessK /access.
     have H3 : nth false (dflatten B1) i1 <= count_one (dflatten B1). exact: leq_nth_count.
      by rewrite (dflatten_countK B1) in H3.
    rewrite -/(daccess _ _).
    destruct c;last first.
     destruct n.
      rewrite -addnA.
      rewrite -[o0 + o3 + o4 + o2]addnA.
      exists (Stay (Good Black (rnode (bnode t t0) (bnode t1 B2)))).
      by rewrite -dB1K /= !catA.
     exists (Stay (Good Black (bnode t B2))).
     by rewrite -dB1K.
     destruct c0,cr => //.
     dependent induction n.
     destruct t.
      dependent induction B2;last first. move: (technical2 d). rewrite /= in x0. by rewrite /= x0.
      exists (Stay (Good Red (rnode (Leaf arr i2 i3) (Leaf arr0 i i0)))).
      by rewrite -dB1K.
     destruct c.
      destruct cl,cr => //.
      exists (Stay (Bad t1 t2 B2)).
      by rewrite -dB1K /= catA.
     exists (Stay (Good Red (rnode (bnode t1 t2) B2))).
     by rewrite -dB1K.
    rewrite -/(daccess _ _).
    destruct cr.
     destruct c => //.
     case (rotateR B1 B2) => rot.
     case => okr rotK.
     case (ddelete _ _ _ _ rot i1 okr oki) => res resK.
     rewrite rotK delete_cat dflatten_sizeK in resK.
     move : resK.
     case: ifP;last by rewrite H.
     move => H' resK.
     rewrite -resK.
     clear resK.
     move: res.
     rewrite !daccessK rotK /access nth_cat dflatten_sizeK.
     case: ifP;last by rewrite H.
     move => H'' res.
     by exists res.
    rewrite -/(daccess _ _).
    rewrite addsubnC;last exact: (sizeW' B1).
    rewrite addsubnC;last exact: leq_access_count.
    dependent destruction n.
    destruct c0.
     set r2b := black_of_red t.
     exists (Stay (Good c (Node i0 i (proj1_sig r2b) B2))).
     by rewrite /= (proj2_sig r2b) -dB1K /=.

    move: n dB1K.
     (* set acc := daccess B1 i1. *)
     rewrite {1}/dflattenn' /dflattenn /dflatten => n dB1K.
     destruct n.
     rewrite -/(dflatten
     => dB1K.
      rewrite -dB1K.
     destruct c.
     rewrite /= in dB1K.
     rewrite daccessK in n.
      destruct c => //.
      rewrite -addnA.
      rewrite -[o0 + o3 + o4 + o2]addnA -dB1K.
      exists (Stay (Good Black (rnode (bnode t t0) (bnode t1 B2)))).
      by rewrite /= -!catA.
    destruct p.
     have okt: (color_ok c (fix_color (Good Black t))). by destruct c.
     case: (balanceL c (Good Black t) B2 okt i0) => res resK.
     exists (Stay res).
     rewrite /= in dB1K.
     by rewrite /= resK /= dB1K.
     destruct cr,c => //.

      dependent destruction B2.
      rewrite [LHS]/= in x0.
      destruct cl,cr => //.
      clear okB1 dB1K.
      rewrite -x0 in B1.
      move: (ddelete _ _ _ (bnode (rnode B1 B2_1) B2_2) i1 erefl oki) => res.
    destruct cl;last first.
     rewrite -/(daccess _) daccessK !addnA {3}/inc_black.
     have H3 : daccess (bnode (rnode B1 B2_1) B2_2) i3 = access (dflatten B1) i3.
      rewrite daccessK /= /access -catA nth_cat dflatten_sizeK.
      case:ifP => //. by rewrite H.
     rewrite -H3.
     rewrite addnA in oki.
      move: (Stay (Good Black (bnode t
                                     (rnode B2_1 B2_2)))).
      move: (rnode_is_not_leaf B0).
      destruct B0 => /= // GUARD4.
      rewrite x0 in B2_1.
      move: (pos_tree_is_not_leaf d B2) => GUARD4.
       by move: (GUARD4 erefl) => /=.
      rewrite /=.

    move: (dflatten_countK B1).
    move: (leq_nth_count i1 .

     destruct c => //.

    destruct c.
     destruct c0 => //.
     dependent induction n.
      destruct B2.
     destruct t.

      dependent destruction B2. move: (technical2 (Param 0)). rewrite /= in x0. by rewrite /= x0.

      rewrite -dB1K. clear x. clear dB1K B2_1 B2_2. destruct B0. move: (technical2 d) => C. by rewrite -[RHS]x0 in C.
      rewrite hht
      move: (technical3 _ _ x0) => H3.
      rewrite -x.
      destruct B0.
      rewrite H3 in B2_1,B2_2.
     ;last first. 
      

     destruct c.
      


     destruct c.
     move: (rnode_is_not_leaf t) => ?.

      dependent induction t.
     exists (Stay (Good Red (rnode t B2))).
     
    dependent induction n.
     set res := 
     destruct c => //.
     rewrite -x in dB1K.
     rewrite -addnA in res.
     exists (Stay (Good Black (rnode (bnode t t0) (bnode t1 B2)))).

    exists (Stay (Good c (Node i i0 n B2))).
    by rewrite -dB1K /=.
   destruct c0, c => //.
    case: (balanceL Black n B2 erefl erefl) => res resK.
    rewrite addsubnC;last exact: (sizeW' B1).
    rewrite addsubnC;last first.
     rewrite -/(daccess _) daccessK /access.
     have H3 : nth false (dflatten B1) i1 <= count_one (dflatten B1). exact: leq_nth_count.
     by rewrite (dflatten_countK B1) in H3.
    dependent induction res.
    destruct c;last first.
     exists (Stay t).
     rewrite /= in resK.
     by rewrite /= resK -dB1K /=.
    rewrite {2}/(inc_black _ _) -/(daccess _).
    exists (Down t).


    have H3 : nth false (dflatten B1) i3 <= count_one (dflatten B1). exact: leq_nth_count.
     by rewrite (dflatten_countK B1) in H3.
    rewrite -/(daccess _).
    have okn : (color_ok Black (fix_color n)) => //. 
    exists (Stay (proj1_sig (balanceL Black n (rnode B2_1 B2_2) okn rb_ok))).
   rewrite /= in B2.
   destruct cr.
    dependent induction B2.
    destruct cl0,cr => //.
    destruct cl;last first.
     rewrite -/(daccess _) daccessK !addnA {3}/inc_black.
     have H3 : daccess (bnode (rnode B1 B2_1) B2_2) i3 = access (dflatten B1) i3.
      rewrite daccessK /= /access -catA nth_cat dflatten_sizeK.
      case:ifP => //. by rewrite H.
     rewrite -H3.
     rewrite addnA in oki.
     move: (ddelete _ _ _ (bnode (rnode B1 B2_1) B2_2) i3 okB oki) => res.
     exists (proj1_sig res).
     rewrite (proj2_sig res) /= !delete_cat size_cat !dflatten_sizeK catA.
     case:ifP. case:ifP => //. by rewrite H.
     rewrite (ltn_addln i3 s1 s0) //.
    clear IHB1 okB IHB2 IHB2_1 IHB2_2.
    dependent induction B1.
    clear IHB1_1 IHB1_2.
    destruct cl,cr => //.
    rewrite /= in x0.
    case_eq (i5 < s1).
     move/idP => H3.
     move (ddelete s1 o1 _ B1_1 i5 _ H3) => dB1 dB1K /=.
     
    rewrite {1}x0. in B1_1.
    move: B0 x => /= B0 x.
    set r2b := (bnode B1_1 B1_2).
    destruct cl,cr => //.
    rewrite -!/(daccess _ _) daccessK.
    rewrite /= /dflatten -!/(dflatten _) /dflatten /access.
    have dfK : dflatten r2b = dflatten B0.
    ewrite -x0.
    dependent inversion B0.
    subst r2b.
    rewrite dflatten_rb /rnode.
    dependent destruction B0.
    inversion B0.
    destruct B0.
    rewrite x0.
    rewrite -/(dflatten (rnode B1_1 B1_2)).
    About JMeq_congr.
    move : (JMeq_congr dflatten x).
    subst r2b => /=.
    rewrite -x.
    rewrite !dflatten_is_dflatten' /=.
    rewrite /= in B0.
    subst r2b => /=.
    rewrite -x.
    -!/(daccess _ _) /=.
    rewrite -x0 in B1_1 B1_2.
    rewrite -{1}x0 -{1}x0.
    move => B2_1 B2_2.
    case (ddelete _ _ _ r2b i5 erefl H) => dB1 dB1K.
    dependent induction dB1.
    move: (balanceL Black n (bnode B2_1 B2_2) (bnode_is_color_ok n) rb_ok) => res.
    subst r2b.
    subst rnd.
    rewrite /bnode /daccess -!/(daccess _ _) /= in res.
    -/(daccess rnd i5).
    exists (Stay (proj1_sig )).

    case dB1.
    case (ddelete s1 o1 _ (bnode B1_1 B1_2) _ _ H) => dB1 dB1K /=.
    move: dB1 dB1K => /= dB1 dB1K.
    dependent induction dB1.
    rewrite addsubnC;last exact: (sizeW' B1).
    rewrite addsubnC;last first.
     rewrite -/(daccess _) daccessK /access.
     have H3 : nth false (dflatten B1) i3 <= count_one (dflatten B1). exact: leq_nth_count.
     by rewrite (dflatten_countK B1) in H3.
    rewrite -/(daccess _).
    have okn : (color_ok Black (fix_color n)) => //. 
    exists (Stay (proj1_sig (balanceL Black n (rnode B2_1 B2_2) okn rb_ok))).
    set B := balanceL _ _ _ _ _.
    rewrite /= in dB1K.
    by rewrite /= (proj2_sig B) /= dB1K.
   dependent induction dB1;last first.
     dependent induction B2. move: (technical2 d). by rewrite x0.
     clear IHB2_2 IHB2_1 x.
     rewrite (technical3 _ _ x0) in B2_1,B2_2.
     have okn : (color_ok c (fix_color n)). dependent induction n => /=. destruct c => //.
     destruct c.
      Check (balanceL Red n B2_1 okn _).
     have okB2_1 : (color_ok c cl). 
     rewrite /= in x0.
     destruct d0,d.
    
      move: (sizeW arr i2) (sizeW arr0 i5) (sizeW arr1 i7) => ? H7 H8.
    move: B1 => /= B1.
    rewrite -r.
    !addnA.
    case_eq dB1.

    clear okB.

    move: B1 => /= B1.
    have okB1 : (wordsize_ok B1).
    destruct B1 => // /=. rewrite leq_eqVlt eq_sym H2 /= in i2.
    apply/andP. split => //. exact: (ltnW i3).
    case (ddelete s1 o1 _ cl B1 _ okB1 H) => dB1 dB1K /=.

     Check (bnode B2_1 B2_2).
    dependent induction B1.
    rewrite /= in x0.
    
     rewrite delete_cat.

      : forall (num ones : nat) (d : param nat) (c : color) (B : tree num ones d c) (i : nat),
            wordsize_ok B -> i < num -> {B' : near_tree' (num - 1) (ones - daccess B i) d c | dflattenn' B' = delete (dflatten B) i}
   Check 
    dependent induction B2.
   case_eq cr.


   have okB1 : (wordsize_ok B1).
    destruct B1 => // /=. clear okB. rewrite leq_eqVlt eq_sym H2 /= in i2.
    apply/andP. split => //. exact: (ltnW i3).
   case (ddelete s1 o1 _ cl B1 _ okB1 H) => dB1 dB1K /=.

   clear okB.
    dependent induction B1;last first.
     destruct c0;last first.
       move: (technical2 d). by rewrite x0.
      rewrite /= in x0.
     
      destruct c => //.
      dependent induction B2_1;last first.
       destruct c => //. move: (technical2 d). rewrite /= in x0. by rewrite /= x0.
      dependent induction B2_2;last first.
       destruct c => //. move: (technical2 d). rewrite /= in x0. by rewrite /= x0.
      rewrite -x /=.
      move: (sizeW arr i2) (sizeW arr0 i5) (sizeW arr1 i7) => ? H7 H8.
   ;last first.

    rewrite /= in dB1K.
    About balanceL.
    Check (balanceL c dB1 (Leaf arr i i2) _ i1).
   case_eq B2 => [arr w1 w2 eq|].
    clear okB.
   destruct B2.
    move: (sizeW arr i2) (i2) (i3) => ? ? ?.
    rewrite leq_eqVlt eq_sym H2 (size_delete1 i) H /= addn1 in i2. 
    rewrite (size_delete1 i) H /= addn1 in i3.
    rewrite addnC -addnBA // subn1 addnC -(size_delete H).
    rewrite [count_one _ + _]addnC -addnBA;last exact: leq_nth_count.
    rewrite [_ + (count_one _ - _)]addnC count_delete.
    by exists (Stay (Good c (Node i0 i1 (Leaf (delete arr i) i2 (ltnW i3)) B2))).
   destruct cr.
   destruct dB1 as [? ? ? ? dB1|? ? ? dB1];last first.
   rewrite /= in dB1K.
   destruct dB1;last first.
   destruct c0;last first.
   destruct cr,c => //.
   rewrite /= in dB1K.
      | BNode ((BNode _ as l),a,RNode (gl,b,gg)) -> bremove (BNode (RNode(l,a,gl),b,gg))
   rewrite /=.
   destruct B2.
   Check (Good c (Node i0 i1 (bnode (rnode t t0) t1) B2)).

   case_eq dB1;last first.

   destruct B1.
    clear okB.
    move: (sizeW arr i2) (i2) (i3) => ? ? ?.
    rewrite leq_eqVlt eq_sym H2 (size_delete1 i) H /= addn1 in i2. 
    rewrite (size_delete1 i) H /= addn1 in i3.
    rewrite addnC -addnBA // subn1 addnC -(size_delete H).
    rewrite [count_one _ + _]addnC -addnBA;last exact: leq_nth_count.
    rewrite [_ + (count_one _ - _)]addnC count_delete.
    by exists (Stay (Good c (Node i0 i1 (Leaf (delete arr i) i2 (ltnW i3)) B2))).

    destruct B2;last first.
    move/implyP: (size_of_node (Node i2 i3 B1_1 B1_2)) => /=.
    rewrite H2 => H3.
    move: (technical1 (w ^ 2 %/ 2) H3) => H4.
    move/eqP: wordsize_sqrn_div2_neq0.
    by rewrite H4 /=.
    dependent induction B2;last first.
    destruct c0;last first.
      move: (technical2 d). by rewrite x0.
     destruct c => //.
     dependent induction B2_1;last first.
      destruct c => //. move: (technical2 d). rewrite /= in x0. by rewrite /= x0.
     dependent induction B2_2;last first.
      destruct c => //. move: (technical2 d). rewrite /= in x0. by rewrite /= x0.
     rewrite -x /=.
     move: (sizeW arr i2) (sizeW arr0 i5) (sizeW arr1 i7) => ? H7 H8.
     

      (* (Black,Param 1) size == w ^ 2 %/ 2 * 2 *)
(* 
(black,d) -> (black,d-1)
Leaf : black -> black
Node : (black,d) -> (black,d.-?)
       red -> red or black
*)


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
       rewrite addsubnC;last first.
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
     rewrite H5 addnC addnA -addnBA // subnn addn0 addnC -size_cat (addsubnC (count_one arr) _ _).
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