(* Xuanrui Qi, Kazunari Tanaka, Jacques Garrigue *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program.
Require Import set_clear Wf_nat Compare_dec ExtrOcamlNatInt.

Tactic Notation "remember_eq" constr(expr) ident(vname) ident(eqname) := case (exist (fun x => x = expr) expr erefl) => vname eqname.

Set Implicit Arguments.

Section dynamic_dependent.

Variable w : nat.
Hypothesis wordsize_gt1: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. exact/ltnW/wordsize_gt1. Qed.

Lemma wordsize_neq0 : w != 0.
Proof. rewrite -lt0n; exact wordsize_gt0. Qed.

Lemma wordsize_sqrn_gt0 : w ^ 2 > 0.
Proof. by rewrite sqrn_gt0 lt0n wordsize_neq0. Qed.

Lemma wordsize_sqrn_gt2 : w ^ 2 > 2.
Proof. by move: wordsize_gt1; case: w => // -[//|] []. Qed.

Lemma wordsize_sqrn_div2_neq0 : w ^ 2 %/ 2 <> 0.
Proof.
by move/eqP; rewrite gtn_eqF // divn_gt0 // (ltn_trans _ wordsize_sqrn_gt2).
Qed.

Section insert.

  Inductive color := Red | Black.

  Inductive tree_ml : Type :=
  | LeafML : forall (arr : seq bool), tree_ml
  | NodeML : forall (sl sr ol or : nat) (c : color) (l r : tree_ml), tree_ml.

  Definition color_ok parent child :=
    match parent, child with
    | Red, Red => false
    | _, _ => true
    end.
  
  Definition incr_black d c :=
    match c with
    | Black => d.+1
    | Red => d
    end.

  Definition is_black c := if c is Black then true else false.

  Lemma incr_black_prop d c : incr_black d c = d + is_black c.
  Proof. case: c => //=. by rewrite addn1. Qed.

  Definition inv c := if c is Black then Red else Black.

  Inductive param (A : Type) : Prop := Param : A -> param A.

  Inductive tree : nat -> nat -> nat -> color -> Type :=
  | Leaf : forall (arr : seq bool),
      (w ^ 2) %/ 2 <= size arr ->
      2 * (w ^ 2) > size arr ->
      tree (size arr) (count_one arr) 0 Black
  | Node : forall {lnum lones rnum rones d cl cr c},
      color_ok c cl -> color_ok c cr ->
      tree lnum lones d cl -> tree rnum rones d cr ->
      tree (lnum + rnum) (lones + rones) (incr_black d c) c.

  Fixpoint tree_size {num ones d c} (t : tree num ones d c) : nat :=
    match t with
    | Leaf _ _ s => 1
    | Node _ _ _ _ _ _ _ _ _ _ l r => tree_size l + tree_size r
    end.

  Lemma tree_size_pos {num ones d c} (B : tree num ones d c) :
    tree_size B > 0.
  Proof.
    elim: B => //= lnum lones rnum rones d' cl cr c' _ _ l IHl r IHr.
    by rewrite addn_gt0 IHl.
  Qed.

  Lemma red_black_ok : color_ok Red Black. 
  Proof. exact. Defined.

  Lemma black_any_ok c : color_ok Black c.
  Proof. exact. Defined.
  
  Definition RNode {lnum lones rnum rones d} (l : tree lnum lones d Black)
    (r : tree rnum rones d Black) : tree (lnum + rnum) (lones + rones) d Red :=
    Node red_black_ok red_black_ok l r.

  Definition BNode {lnum lones rnum rones d cl cr}
    (l : tree lnum lones d cl) (r : tree rnum rones d cr) :
    tree (lnum + rnum) (lones + rones) d.+1 Black :=
    Node (black_any_ok cl) (black_any_ok cr) l r.

  Inductive ins_tree : nat -> nat -> nat -> color -> Type :=
  | Fix : forall {num1 ones1 num2 ones2 num3 ones3 d},
      tree num1 ones1 d Black -> tree num2 ones2 d Black ->
      tree num3 ones3 d Black ->
      ins_tree (num1 + num2 + num3) (ones1 + ones2 + ones3) d Red
  | Tr : forall {num ones d c} pc, tree num ones d c -> ins_tree num ones d pc.

  
  Definition ins_tree_color {nums ones d c} (t : ins_tree nums ones d c) :=
    match t with
    | Fix _ _ _ _ _ _ _ _ _ _ => Red
    | Tr _ _ _ _ _ _ => Black
    end.


  Definition black_of_fix {num ones d c} (t : ins_tree num ones d c) :=
    match t with
    | Fix _ _ _ _ _ _ _ _ _ _ => Black
    | Tr _ _ _ c _ _ => c
    end.

  Definition fix_ins_tree {num ones d c} (t : ins_tree num ones d c) :
    tree num ones (incr_black d (inv (ins_tree_color t))) (black_of_fix t) :=
    match t with
    | Fix _ _ _ _ _ _ _ t1 t2 t3 => BNode (RNode t1 t2) t3
    | Tr _ _ _ _ _ t' => t'
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

  Definition dflatteni {num ones d c} (B : ins_tree num ones d c) :=
    match B with
    | Fix _ _ _ _ _ _ _ t1 t2 t3 => dflatten t1 ++ dflatten t2 ++ dflatten t3
    | Tr _ _ _ _ _ t' => dflatten t'
    end.

  (* 
   * Translated from https://github.com/xuanruiqi/dtp/blob/master/RedBlack.idr
   * which in turn is translated from dynamic_dependent.v
   *)
  Program Definition balanceL {lnum lones rnum rones d cl cr} (c : color)
            (l : ins_tree lnum lones d cl)
            (r : tree rnum rones d cr)
            (ok_l : color_ok c (ins_tree_color l))
            (ok_r : color_ok c cr) :
    { t' : ins_tree (lnum + rnum) (lones + rones) (incr_black d c) c |
      dflatteni t' = dflatteni l ++ dflatten r } :=
    match c with
    | Black =>
      match l with
      | Fix _ _ _ _ _ _ _ t1 t2 t3 => Tr Black (RNode (BNode t1 t2) (BNode t3 r))
      | Tr _ _ _ _ _ l' => Tr Black (BNode l' r)
      end
    | Red => match cr with
            | Red => _ (* impossible *)
            | Black => match l with
                      | Fix _ _ _ _ _ _ _ _ _ _ => _ (* impossible *)
                      | @Tr _ _ _ c' _ l' =>
                        match c' with
                        | Red =>
                          match l' with
                          | Leaf _ _ _ => _ (* impossible *)
                          | @Node _ _ _ _ _ cll clr _ _ _ t1 t2 =>
                            match cll with
                            | Black => match clr with
                                      | Black => Fix t1 t2 r
                                      | Red => _ (* impossible *)
                                      end
                            | Red => _ (* impossible *)
                            end
                          end
                        | Black => Tr Red (RNode l' r)
                        end
                      end
            end
    end.

  Next Obligation. by rewrite addnA. Qed.

  Next Obligation. by rewrite addnA. Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceL_obligation_2 => //=.
    destruct balanceL_obligation_3 => //=.
    by rewrite -Heq_l //= -!catA.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceL_obligation_7 => //=.
    by rewrite -Heq_l.
  Qed.

  Next Obligation. subst l; by move: ok_l. Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceL_obligation_18 => //=.
    by rewrite -Heq_l -Heq_l' //= catA.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceL_obligation_28 => //=.
    by rewrite -Heq_l.
  Qed.


  Program Definition balanceR {lnum lones rnum rones d cl cr} (c : color)
            (l : tree lnum lones d cl)
            (r : ins_tree rnum rones d cr)
            (ok_l : color_ok c cl)
            (ok_r : color_ok c (ins_tree_color r)) :
    { t' : ins_tree (lnum + rnum) (lones + rones) (incr_black d c) c |
      dflatteni t' = dflatten l ++ dflatteni r } :=
    match c with
    | Black =>
      match r with
      | Fix _ _ _ _ _ _ _ t1 t2 t3 => Tr Black (RNode (BNode l t1) (BNode t2 t3))
      | Tr _ _ _ _ _ r' => Tr Black (BNode l r')
      end
    | Red => match cl with
            | Red => _ (* impossible *)
            | Black => match r with
                      | Fix _ _ _ _ _ _ _ _ _ _ => _ (* impossible *)
                      | @Tr _ _ _ c' _ r' =>
                        match c' with
                        | Red =>
                          match r' with
                          | Leaf _ _ _ => _ (* impossible *)
                          | @Node _ _ _ _ _ cll clr _ _ _ t1 t2 =>
                            match cll with
                            | Black => match clr with
                                      | Black => Fix l t1 t2
                                      | Red => _ (* impossible *)
                                      end
                            | Red => _ (* impossible *)
                            end
                          end
                        | Black => Tr Red (RNode l r')
                        end
                      end
            end
    end.

  Next Obligation. by rewrite !addnA. Qed.

  Next Obligation. by rewrite !addnA. Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct balanceR_obligation_3, balanceR_obligation_4 => //=.
    by rewrite -Heq_r //= !catA.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceR_obligation_7 => //=.
    by rewrite -Heq_r.
  Qed.

  Next Obligation. subst r; by move: ok_r. Qed.

  Next Obligation. by rewrite addnA. Qed.

  Next Obligation. by rewrite addnA. Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct balanceR_obligation_18, balanceR_obligation_19 => //=.
    by rewrite -Heq_r -Heq_r'.
  Qed.

  Next Obligation.
    rewrite /eq_rect. destruct balanceR_obligation_27 => //=.
    by rewrite -Heq_r.
  Qed.

  Lemma dflatten_size num ones d c (B : tree num ones d c) :
    num = size (dflatten B).
  Proof.
    elim: B => //= lnum lones rnum rones d' cl cr c' ok_l ok_r l IHl r IHr.
    by rewrite size_cat -IHl -IHr.
  Qed.

  Program Fixpoint dins {num ones d c}
    (B : tree num ones d c)
    (b : bool) (i : nat) {measure (tree_size B) } :
    { B' : ins_tree num.+1 (ones + b) d c |
      dflatteni B' = insert1 (dflatten B) b i } :=
    match B with
    | Leaf s _ _ => 
      let s' := insert1 s b i in
      (* cannot use "if" due to bugs in Program *)
      match (size s' == 2 * (w ^ 2)) with
      | true => (* split the node *)
        let n := (size s') %/ 2 in
        let sl := take n s' in
        let sr := drop n s' in
        Tr c (RNode (Leaf sl _ _) (Leaf sr _ _))
      | false => Tr c (Leaf s' _ _)
      end
    | Node lnum _ _ _ _ _ _ _ ok_l ok_r l r =>
      if i < lnum
      then (` (balanceL c (dins l b i) r _ ok_r))
      else (` (balanceR c l (dins r b (i - lnum)) ok_l _))
    end.

  Next Obligation.
    move/eqP/eqnP: Heq_anonymous => -> //=.
    rewrite size_take size_insert1 mulKn //=. 
    case: ifP => H. exact: leq_div.
    apply: leq_trans. apply: wildcard'.
    by rewrite leq_eqVlt ltnSn orbT.
  Qed.

  Next Obligation.
    move/eqP/eqnP: Heq_anonymous => -> //=.
    rewrite size_take size_insert1 mulKn //=.
    case: ifP => H. by rewrite ltn_Pmull //= expn_gt0 wordsize_gt0.
    move/negbT: H. rewrite -leqNgt => H.
    apply: leq_ltn_trans. apply: H.
    by rewrite ltn_Pmull //= expn_gt0 wordsize_gt0.
  Qed.

  Next Obligation.
    move/eqP/eqnP: Heq_anonymous => //=.
    rewrite size_drop size_insert1 => ->.
    by rewrite mulKn //= mulSn mul1n -addnBA // subnKC // leq_div.
  Qed.

  Next Obligation.
    move/eqP/eqnP: Heq_anonymous => //=.
    rewrite size_drop size_insert1 => ->.
    rewrite mulKn //= mulSn mul1n -addnBA // subnKC //.
    by rewrite -{1}[w ^ 2]addn0 ltn_add2l expn_gt0 wordsize_gt0.
  Qed.

  Next Obligation. by rewrite -size_cat cat_take_drop size_insert1. Qed.

  Next Obligation.
    rewrite -count_cat cat_take_drop /count_one count_insert1. by destruct b.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct dins_func_obligation_7, dins_func_obligation_6, dins_func_obligation_5 => //=.
    by rewrite cat_take_drop.
  Qed.

  Next Obligation.
    rewrite size_insert1. exact: leq_trans.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP: Heq_anonymous => /=.
    rewrite size_insert1 neq_ltn. case/orP => //.
    by rewrite ltnNge wildcard'0.
  Qed.

  Next Obligation. by rewrite size_insert1. Qed.

  Next Obligation. rewrite /count_one count_insert1. by destruct b. Qed.

  Next Obligation.
    rewrite /eq_rect.
    by destruct dins_func_obligation_13, dins_func_obligation_12, dins_func_obligation_11.
  Qed.

  Next Obligation.
    apply/ltP. by rewrite -Heq_B /= -[X in X < _]addn0 ltn_add2l tree_size_pos.
  Qed.
  
  Next Obligation. by destruct dins, x, c. Qed.

  Next Obligation.
    apply/ltP. by rewrite -Heq_B /= -[X in X < _]add0n ltn_add2r tree_size_pos.
  Qed.
    
  Next Obligation. by destruct dins, x, c. Qed.
  
  Next Obligation. by rewrite -addn1 -[in RHS]addn1 addnAC addnA. Qed.

  Next Obligation. by rewrite addnAC addnA. Qed.

  Next Obligation. by rewrite addnAC. Qed.

  Next Obligation.
    case: ifP => /= H.
    - set B' := balanceL _ _ _ _ _.
      destruct dins_func_obligation_23.
      rewrite (proj2_sig B') {B'}.
      destruct dins => /=.
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
    - set B' := balanceR _ _ _ _ _.
      rewrite /dflatteni /eq_rect => //=.
      destruct dins_func_obligation_23, dins_func_obligation_22, dins_func_obligation_21.
      rewrite -/(dflatteni (proj1_sig B')) (proj2_sig B') {B'}.
      destruct dins => //=.
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
  Qed.

 Program Definition paint_black {num ones d c} (B : tree num ones d c) :
   { B' : tree num ones (incr_black d (inv c)) Black |
     dflatten B' = dflatten B } :=
   match B with
   | Leaf _ _ _ => B
   | Node _ _ _ _ _ _ _ _ _ _ l r => BNode l r
   end.

 Next Obligation.
   rewrite /eq_rect.
   destruct paint_black_obligation_4 => //=. by rewrite -Heq_B.
 Qed.

 Next Obligation. by destruct c. Qed.

 Next Obligation. rewrite /eq_rect. by destruct paint_black_obligation_6. Qed.

 Definition dinsert {num ones d c}
   (B : tree num ones d c) (b : bool) (i : nat) :=
   (` (paint_black (fix_ins_tree (` (dins B b i))))).

 Lemma fix_ins_treeK {num ones d c} (t : ins_tree num ones d c) :
   dflatten (fix_ins_tree t) = dflatteni t.
 Proof.
   case: t => //= num1 ones1 num2 ones2 num3 ones3 d' t1 t2 t3.
   by rewrite catA.
 Qed.

 Theorem dinsertK {num ones d c} (B : tree num ones d c) (b : bool) (i : nat) :
   dflatten (dinsert B b i) = insert1 (dflatten B) b i.
 Proof.
   rewrite /dinsert. destruct dins, paint_black => //=.
   by rewrite e0 //= fix_ins_treeK e.
 Qed.

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

  Lemma dflatten_ones {num ones d c} (B : tree num ones d c) :
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

  Lemma access_leq_count (s : seq bool) i : i < size s -> access s i <= count_one s.
  Proof.
    rewrite /access.
    elim: s i => //= h s IHs i H.
    case_eq i => [| i'] //= Hi'. by case: h.
    apply: leq_trans. apply: IHs. move: H. by rewrite Hi' ltnS.
    by rewrite leq_addl.
  Qed.
    
  Lemma daccess_leq_ones {num ones d c} (B : tree num ones d c) i :
    i < num -> daccess B i <= ones.
  Proof.
    elim: B i => [s w_wf size_wf | lnum lones rnum rones d' cl cr c' ok_l ok_r l IHl r IHr] //= i H.
    by rewrite /count_one access_leq_count.
    case: ifP => Hi.
    apply: leq_trans. exact: IHl. exact: leq_addr.
    apply: leq_trans. apply: IHr.
    rewrite -(ltn_add2r lnum) addnC addnBA.
    by rewrite addnC addnK addnC. by rewrite leqNgt Hi. 
    by rewrite leq_addl.
  Qed.
    
End query.


Section set_clear.

  Obligation Tactic := idtac.
  
  Program Fixpoint bset {num ones d c} (B : tree num ones d c) i
    {measure (tree_size B)} :
    { B'b : tree num (ones + (~~ (daccess B i)) && (i < num)) d c * bool
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
    by rewrite -addn1 leq_add2l tree_size_pos.
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
    by rewrite -add1n leq_add2r tree_size_pos.
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

  
  Program Fixpoint bclear {num ones d c}
    (B : tree num ones d c) i
    { measure (tree_size B) } :
    { B'b : tree num (ones - (daccess B i) && (i < num)) d c * bool |
      dflatten B'b.1 = bit_clear (dflatten B) i /\ snd B'b = daccess B i } :=

    match B with
    | Leaf s _ _ => (Leaf (bit_clear s i) _ _, access s i)
    | Node lnum lones rnum rones _ _ _ _ col cor l r =>
      match lt_dec i lnum with
      | left H =>
        let l'b := bclear l i
        in (Node col cor l'b.1 r, l'b.2)
      | right H =>
        let r'b := bclear r (i - lnum)
        in (Node col cor l r'b.1, r'b.2)
      end
    end.

  Next Obligation. intros. by rewrite size_bit_clear. Qed.

  Next Obligation. intros. by rewrite size_bit_clear. Qed.

  Next Obligation. intros. by rewrite size_bit_clear. Qed.

  Next Obligation.
    intros. case Hi: (i < size s).
    + by rewrite /count_one //= (count_bit_clear false) //= andbT.
    + rewrite bit_clear_over //=. by rewrite andbF subn0.
      by rewrite leqNgt Hi.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    by destruct bclear_func_obligation_4, bclear_func_obligation_3.
  Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    by rewrite -Heq_B //= -addn1 leq_add2l tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst => //=.
    move/ltP: (H) => Hi /=.
    rewrite Hi ltn_addr //= andbT.
    rewrite addnC addnBA. by rewrite addnC. by rewrite daccess_leq_ones.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct bclear_func_obligation_7 => //=.
    move/ltP : (H) => Hi /=.
    rewrite /proj1_sig; subst l'b. destruct bclear => //=.
    split.
    + rewrite (proj1 a) /bit_clear update_cat dflatten_sizeK.
      by rewrite Hi.
    + by rewrite (proj2 a) Hi.
  Qed.

  Next Obligation.
    intros; subst. rewrite -Heq_B //=. apply/ltP.
    by rewrite -[X in X < _]add0n ltn_add2r tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst => //=.
    move/ltP: (H) => Hi /=. rewrite -if_neg Hi.
    case Hi': (i - lnum < rnum); move: (Hi'); rewrite -(ltn_add2l lnum) subnKC;
    try move => ->.
    + rewrite andbT addnBA //= daccess_leq_ones //= Hi' //=.
      by rewrite leqNgt Hi.
    + by rewrite andbF !subn0.
      by rewrite leqNgt Hi.
  Qed.

  Next Obligation.
     split; subst; last first.
      destruct bclear as [[r' tgt][Hr' Hf]] => /=.
      move/ltP: (H) => Hi.
      by rewrite -if_neg Hi -Hf.
    move=> /=.
    move: (lones + rones - _) (bclear_func_obligation_10 _ _ _ _ _ _) => ones Ho.
    destruct Ho => /=.
    destruct bclear as [[r' tgt][Hr' Hf]] => /=.
    rewrite /= in Hr'.
    move/ltP: (H).
    rewrite Hr' /bit_clear update_cat -(dflatten_size l) => Hi.
    by rewrite -if_neg Hi.
  Qed.

  Next Obligation. intuition. Qed.

    
End set_clear.

Section delete.

  Lemma count_delete_tr {num ones} (tr : tree num ones 0 Black) i :
    ones - (daccess tr i) = count_one (delete (dflatten tr) i).
  Proof.
    remember_eq 0 d' deq. remember_eq Black c' ceq. move: tr.
    rewrite -deq -ceq => tr.
    destruct tr => //=. by rewrite count_delete.
    move: deq. by rewrite ceq.
  Qed.

  Inductive del_tree : nat -> nat -> nat -> color -> Type :=
  | Stay : forall {num ones d c} pc,
      color_ok c (inv pc) -> tree num ones d c -> del_tree num ones d pc
  | Down : forall {num ones d}, tree num ones d Black -> del_tree num ones d.+1 Black.

  Definition dflattend {num ones d c} (tr : del_tree num ones d c) :=
    match tr with
    | Stay _ _ _ _ _ _ t => dflatten t
    | Down _ _ _ t => dflatten t
    end.

  Lemma wordsize_sqrn_div2_gt0 : 0 < w ^ 2 %/ 2.
  Proof.
    rewrite lt0n. apply/eqP. apply: wordsize_sqrn_div2_neq0.
  Qed.

  Lemma wordsize_del_lt_twice : (w ^ 2 %/ 2 + (w ^ 2 %/ 2).-1 < 2 * w ^ 2).
  Proof.
    have Hw: (w ^ 2 %/ 2 + (w ^ 2 %/ 2).-1 < w ^ 2).
    rewrite -subn1 addnBA divn2. rewrite addnn.
    rewrite -[X in _ < X]odd_double_half subn1.
    have Hw': (((w ^ 2)./2).*2.-1 < ((w ^ 2)./2).*2).
    rewrite -subn1 -[X in _ < X]subn0 ltn_sub2l //=.
    by rewrite -[X in X < _]double0 ltn_double -divn2 wordsize_sqrn_div2_gt0.
    apply: leq_trans. apply: Hw'. apply: leq_addl.
    by rewrite -divn2 wordsize_sqrn_div2_gt0.
    apply: leq_trans. apply: Hw. exact: leq_pmull.  
  Qed.

  Lemma bool_true b : b = (b == true).
  Proof. by case: b. Qed.

  Lemma cons_del_head s : size s > 0 -> access s 0 :: delete s 0 = s.
  Proof.
    case: s => //= h s H.
    by rewrite /delete //= drop0.
  Qed.
  
  Program Definition merge_arrays
    (s1 s2 : seq bool) (i : nat)
    (w_ok1 : w ^ 2 %/ 2 == size s1)
    (w_ok2 : w ^ 2 %/ 2 == size s2)
    (Hi : i < size s1 + size s2) :
    { tr : tree (size s1 + size s2 - 1)
                (count_one s1 + count_one s2 - access (s1 ++ s2) i) 0 Black |
      dflatten tr = delete (s1 ++ s2) i } :=
    if i < size s1 is true
    then Leaf ((rcons (delete s1 i) (access s2 0)) ++ (delete s2 0)) _ _
    else Leaf (s1 ++ (delete s2 (i - size s1))) _ _.

  Next Obligation.
    rewrite size_cat size_rcons.
    case Hi': (i < size s1).
    + rewrite !size_delete. rewrite -(eqP w_ok1) -(eqP w_ok2). 
      rewrite prednK. exact: leq_addr. exact: wordsize_sqrn_div2_gt0.
      by rewrite -(eqP w_ok2) wordsize_sqrn_div2_gt0. by rewrite Hi'.
    + rewrite delete_oversize //=. rewrite size_delete.
      rewrite -[X in _ <= X + _]addn1 -(eqP w_ok1). rewrite addnAC -addnA.
      apply: leq_addr. by rewrite -(eqP w_ok2) wordsize_sqrn_div2_gt0.
      by rewrite leqNgt Hi'.
  Qed.

  Next Obligation.
    rewrite size_cat size_rcons.
    case Hi': (i < size s1).
    + rewrite !size_delete. rewrite -(eqP w_ok1) -(eqP w_ok2).
      rewrite prednK. apply: wordsize_del_lt_twice.
      apply: wordsize_sqrn_div2_gt0.
      by rewrite -(eqP w_ok2) wordsize_sqrn_div2_gt0.
      by rewrite Hi'.
    + rewrite delete_oversize. rewrite size_delete.
      rewrite -(eqP w_ok1) -(eqP w_ok2).
      rewrite addSnnS prednK.
      by rewrite addnn mul2n ltn_double ltn_Pdiv //= wordsize_sqrn_gt0.
      apply: wordsize_sqrn_div2_gt0. by rewrite -(eqP w_ok2) wordsize_sqrn_div2_gt0.
      by rewrite leqNgt Hi'.
  Qed.

  Next Obligation.
    rewrite size_cat size_rcons !size_delete ?prednK.
    by rewrite -subn1 addnBA //= -(eqP w_ok2) wordsize_sqrn_div2_gt0.
    by rewrite -(eqP w_ok1) wordsize_sqrn_div2_gt0.
    by rewrite -?(eqP w_ok2) wordsize_sqrn_div2_gt0.
    by rewrite -Heq_anonymous.
  Qed.

  Next Obligation.
    rewrite /count_one. rewrite -[in LHS]cats1 count_cat count_cat.
    rewrite -/count_one -!count_delete.
    rewrite /access nth_cat -Heq_anonymous //= addn0.
    rewrite -addnA -bool_true subnKC.
    by rewrite addnC [in RHS]addnC addnBA //= -/access access_leq_count.
    have Hmatch: (match s2 with
                  | []%list => false
                  | x :: _ => x
                  end = access s2 0). by rewrite /access.
    by rewrite Hmatch access_leq_count //= -(eqP w_ok2) wordsize_sqrn_div2_gt0. 
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct merge_arrays_obligation_3, merge_arrays_obligation_4 => //=.
    have Hmatch: (match s2 with
                  | []%list => false
                  | x :: _ => x
                  end = access s2 0). by rewrite /access.
    rewrite Hmatch -cats1 -catA cat1s. rewrite cons_del_head.
    rewrite /delete take_cat -Heq_anonymous -catA drop_cat.
    case: ifP => Hi' //=.
    rewrite drop_oversize //=.
    have H: (i.+1 - size s1 == 0). by rewrite subn_eq0 -Heq_anonymous.
    by rewrite (eqP H) drop0.
    move/negbT: Hi'. by rewrite -leqNgt => ->.
    by rewrite -(eqP w_ok2) wordsize_sqrn_div2_gt0.
  Qed.

  Next Obligation.
    by rewrite size_cat -(eqP w_ok1) leq_addr.
  Qed.

  Next Obligation.
    rewrite size_cat. rewrite size_delete.
    rewrite -(eqP w_ok1) -(eqP w_ok2). 
    apply: wordsize_del_lt_twice.
    rewrite -(ltn_add2r (size s1)) subnK. by rewrite addnC.
    move/eqP/eqnP/eqP: H. by rewrite subn_eq0 -leqNgt.
  Qed.

  Next Obligation.
    rewrite size_cat. rewrite size_delete.
    by rewrite -subn1 addnBA //= -(eqP w_ok2) wordsize_sqrn_div2_gt0.
    rewrite -(ltn_add2r (size s1)) subnK. by rewrite addnC.
    move/eqP/eqnP/eqP: H. by rewrite subn_eq0 -leqNgt.
  Qed.

  Next Obligation.
    rewrite /count_one count_cat -/count_one. rewrite -count_delete.
    rewrite /access. rewrite nth_cat.
    case: ifP => H' //=. move: H. by rewrite H'.
    rewrite addnBA //= -/access access_leq_count //=.
    rewrite -(ltn_add2r (size s1)) subnK. by rewrite addnC.
    move/eqP/eqnP/eqP: H. by rewrite subn_eq0 -leqNgt.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct merge_arrays_obligation_9, merge_arrays_obligation_8 => //=.
    rewrite /delete take_cat.
    move/eqP/eqnP/eqP: H. rewrite subn_eq0. move/negbTE => H.
    rewrite H //=. rewrite drop_cat.
    move/negbT: (H). rewrite -ltnNge => H'.
    rewrite ltnNge leq_eqVlt H' orbT //= subSn.
    rewrite catA //=. by rewrite leqNgt H.
  Qed.

  Definition delete_last (s : seq bool) := delete s (size s).-1.

  Definition blast (s : seq bool) := access s (size s).-1.

  
  Program Definition delete_from_leaves {lnum lones rnum rones : nat}
    (pc : color)
    (l : tree lnum lones 0 Black)
    (r : tree rnum rones 0 Black)
    (i : nat) :
    { B' : del_tree (lnum + rnum - (i < lnum + rnum))
                    (lones + rones - access (dflatten l ++ dflatten r) i)
                    (incr_black 0 pc) pc
    | dflattend B' = delete (dflatten l ++ dflatten r) i} :=
    match l with
    | Leaf arr1 _ _ =>
      match r with
      | Leaf arr2 _ _ =>
        if i < size arr1 is true
        then if w ^ 2 %/ 2 == size arr1 is true
             then if w ^ 2 %/ 2 == size arr2 is true
                  then
                    let ret := (` (merge_arrays arr1 arr2 i _ _ _)) in
                    match pc with
                    | Red => Stay Red _ ret
                    | Black => Down ret
                    end
                  else
                    match pc with
                    | Red => Stay Red _ (RNode
                                          (Leaf (rcons (delete arr1 i)
                                                       (access arr2 0)) _ _)
                                          (Leaf (delete arr2 0) _ _))
                    | Black => Stay Black _ (BNode
                                              (Leaf (rcons (delete arr1 i)
                                                           (access arr2 0)) _ _)
                                              (Leaf (delete arr2 0) _ _))
                    end
             else
               match pc with
               | Red => Stay Red _ (RNode
                                     (Leaf (delete arr1 i) _ _)
                                     (Leaf arr2 _ _))
               | Black => Stay Black _ (BNode
                                         (Leaf (delete arr1 i) _ _)
                                         (Leaf arr2 _ _))
               end
        else
          if i < size arr1 + size arr2 is true
          then if w ^ 2 %/ 2 == size arr2 is true
               then if w ^ 2 %/ 2 == size arr1 is true
                    then
                      let ret := (` (merge_arrays arr1 arr2 i _ _ _)) in
                      match pc with
                      | Red => Stay Red _ ret
                      | Black => Down ret
                      end
                    else
                      match pc with
                      | Red => Stay Red _
                                   (RNode (Leaf (delete_last arr1) _ _)
                                          (Leaf ((blast arr1) ::
                                                 (delete arr2 (i - size arr1)))
                                            _ _))
                      | Black => Stay Black _
                                     (BNode (Leaf (delete_last arr1) _ _)
                                            (Leaf ((blast arr1) ::
                                                   (delete arr2 (i - size arr1)))
                                              _ _))
                      end
               else
                 match pc with
                 | Red => Stay Red _ (RNode (Leaf arr1 _ _)
                                           (Leaf (delete arr2 (i - size arr1)) _ _))
                 | Black => Stay Black _ (BNode (Leaf arr1 _ _)
                                               (Leaf (delete arr2 (i - size arr1)) _ _))
                 end
          else
            match pc with
            | Red => Stay Red _ (RNode (Leaf arr1 _ _) (Leaf arr2 _ _))
            | Black => Stay Black _ (BNode (Leaf arr1 _ _) (Leaf arr2 _ _))
            end
      | Node _ _ _ _ _ _ _ _ _ _ _ _  => _
      end
    | Node _ _ _ _ _ _ _ _ _ _ _ _ => _
    end.
   
  Next Obligation.
    have H: i < size arr1. by rewrite -Heq_anonymous4.
    apply: leq_trans. apply: H. apply: leq_addr.
  Qed.

  Next Obligation.
    have H: i < size arr1. by rewrite -Heq_anonymous4.
    have H': (i < size arr1 + size arr2).
    apply: leq_trans. apply: H. apply: leq_addr. by rewrite H'.
  Qed.

  Next Obligation.
    by rewrite /access !nth_cat -Heq_l -Heq_anonymous4.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_6, delete_from_leaves_obligation_5 => //=.
    destruct merge_arrays. by rewrite /proj1_sig //= -Heq_l -Heq_r.
  Qed.

  Next Obligation.
    have H: i < size arr1. by rewrite -Heq_anonymous4.
    have H': (i < size arr1 + size arr2).
    apply: leq_trans. apply: H. apply: leq_addr. by rewrite H'.
  Qed.

  Next Obligation.
    by rewrite /access !nth_cat -Heq_l -Heq_anonymous4.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_9, delete_from_leaves_obligation_8 => //=.
    destruct merge_arrays. by rewrite /proj1_sig //= -Heq_l -Heq_r. 
  Qed.

  Next Obligation.
    rewrite -cats1 size_cat //= size_delete. rewrite addn1 prednK //=.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
    by rewrite -Heq_anonymous4.
  Qed.

  Next Obligation.
    rewrite -cats1 size_cat //= size_delete. rewrite addn1 prednK //=.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
    by rewrite -Heq_anonymous4.
  Qed.

  Next Obligation.
    move: (wildcard'3). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H => -> //=.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite size_delete //=. apply: leq_ltn_trans.
    apply: leq_pred. exact.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -cats1 size_cat //= !size_delete //= addn1 prednK //=.
    have H': (i < size arr1 + size arr2).
    move/eqP/eqnP/eqP: Heq_anonymous4 => H'.
    apply: leq_trans. apply: H'. apply: leq_addr. 
    rewrite H' -subn1 addnBA //=.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
  Qed.

  Next Obligation.
    rewrite -cats1. rewrite /count_one count_cat /=.
    have Hmatch: (match arr2 with
                  | []%list => false
                  | x :: _ => x
                  end = access arr2 0). by rewrite /access.
    rewrite /access nth_cat -Heq_l /= -Heq_anonymous4 Hmatch.
    rewrite -bool_true /access addn0.
    rewrite [in RHS]addnC -/access -/count_one.
    rewrite -addnBA. rewrite count_delete.
    rewrite -[X in _ + _ + X = _]count_delete.
    rewrite -addnA subnKC. by rewrite addnC.
    apply: access_leq_count. apply: leq_trans.
    apply: wordsize_sqrn_div2_gt0. exact.
    apply: access_leq_count. by rewrite -Heq_anonymous4.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_17, delete_from_leaves_obligation_16 => //=.
    rewrite -cats1 delete_catL -Heq_l //= -Heq_r //= -catA.
    destruct arr2 => //=.
    have Habsurd: (~~ ((w ^ 2 %/ 2) <= 0)).
    rewrite -ltnNge. apply: wordsize_sqrn_div2_gt0.
    move: (wildcard'3) => //=. move/negbTE: Habsurd => -> //=.
    by rewrite /delete /= drop0.
  Qed.

  Next Obligation.
    rewrite -cats1 size_cat //= size_delete //= addn1 prednK //=.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
  Qed.


  Next Obligation.
    rewrite -cats1 size_cat //= size_delete //= addn1 prednK //=.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
  Qed.

  Next Obligation.
    move: (wildcard'3). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H => -> //=.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
  Qed.

  Next Obligation.
    rewrite size_delete. apply: leq_ltn_trans. apply: leq_pred. exact.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
  Qed.

  Next Obligation.
    have H': i < size arr1. by rewrite -Heq_anonymous4.
    have H1: 0 < size arr1.
    move/eqP/eqnP: Heq_anonymous5 => <-. apply: wordsize_sqrn_div2_gt0.
    have H2: 0 < size arr2. apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -cats1 size_cat //= !size_delete //= addn1 prednK //=. 
    have H'': (i < size arr1 + size arr2).
    apply: leq_trans. apply: H'. apply: leq_addr.
    by rewrite H'' -subn1 //= addnBA.
  Qed.

  Next Obligation.
    rewrite -cats1. rewrite /count_one count_cat /=.
    have Hmatch: (match arr2 with
                  | []%list => false
                  | x :: _ => x
                  end = access arr2 0). by rewrite /access.
    rewrite /access nth_cat -Heq_l /= -Heq_anonymous4 Hmatch.
    rewrite -bool_true /access addn0.
    rewrite [in RHS]addnC -/access -/count_one.
    rewrite -addnBA. rewrite count_delete.
    rewrite -[X in _ + _ + X = _]count_delete.
    rewrite -addnA subnKC. by rewrite addnC.
    apply: access_leq_count. apply: leq_trans.
    apply: wordsize_sqrn_div2_gt0. exact.
    apply: access_leq_count. by rewrite -Heq_anonymous4.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_25, delete_from_leaves_obligation_24 => //=.
    rewrite -cats1 delete_catL -Heq_l //= -Heq_r //= -catA.
    destruct arr2 => //=.
    have Habsurd: (~~ ((w ^ 2 %/ 2) <= 0)).
    rewrite -ltnNge. apply: wordsize_sqrn_div2_gt0.
    move: (wildcard'3) => //=. move/negbTE: Habsurd => -> //=.
    by rewrite /delete /= drop0.
  Qed.

  Next Obligation.
    move: (wildcard'1). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H => -> //=.
    have Harr2: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite size_delete //=. apply: leq_ltn_trans.
    apply: leq_pred. exact.
  Qed.

  Next Obligation.
    have H': i < size arr1. by rewrite -Heq_anonymous4.
    have H'': (i < size arr1 + size arr2).
    apply: leq_trans. apply: H'. apply: leq_addr.
    rewrite size_delete //= H'' -subn1 //=.
    rewrite addnC addnBA. by rewrite [in LHS]addnC.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
  Qed.

  Next Obligation.
    rewrite /access nth_cat -count_delete -Heq_l //= -Heq_anonymous4 /access.
    rewrite addnC addnBA. by rewrite addnC.
    by rewrite -/access access_leq_count.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_34, delete_from_leaves_obligation_33 => //=.
    by rewrite -Heq_l -Heq_r //= delete_catL.
  Qed.

  Next Obligation.
    move: (wildcard'1). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H => -> //=.
    have Harr2: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite size_delete //=. apply: leq_ltn_trans.
    apply: leq_pred. exact.
  Qed.

  Next Obligation.
    have H': i < size arr1. by rewrite -Heq_anonymous4.
    have H'': (i < size arr1 + size arr2).
    apply: leq_trans. apply: H'. apply: leq_addr.
    rewrite size_delete //= H'' -subn1 //=.
    rewrite addnC addnBA. by rewrite [in LHS]addnC.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
  Qed.

  Next Obligation.
    rewrite /access nth_cat -count_delete -Heq_l //= -Heq_anonymous4 /access.
    rewrite addnC addnBA. by rewrite addnC.
    by rewrite -/access access_leq_count.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_42, delete_from_leaves_obligation_41 => //=.
    by rewrite -Heq_l -Heq_r //= delete_catL.
  Qed.

  Next Obligation. by rewrite -Heq_anonymous5. Qed.

  Next Obligation. by rewrite -Heq_l -Heq_r. Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_50, delete_from_leaves_obligation_49 => //=.
    destruct merge_arrays. by rewrite /proj1_sig -Heq_l -Heq_r.
  Qed.

  Next Obligation. by rewrite -Heq_anonymous5. Qed.

  Next Obligation. by rewrite -Heq_l -Heq_r. Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_53, delete_from_leaves_obligation_52 => //=.
    destruct merge_arrays. by rewrite /proj1_sig -Heq_l -Heq_r.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP/negbTE: H0 => H0.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /delete_last size_delete //=.
    move: (wildcard'1). rewrite leq_eqVlt H0 //= => H0'.
    by rewrite -(leq_add2r 1) !addn1 prednK.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /delete_last size_delete //=.
    apply: leq_ltn_trans. apply: leq_pred. exact.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    rewrite size_delete. rewrite prednK //=.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
  Qed.

  Next Obligation.
    rewrite size_delete. rewrite prednK //=.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -Heq_anonymous5 /delete_last !size_delete.
    rewrite prednK. rewrite -subn1. by rewrite addnC addnBA //= addnC.
    move/eqP/eqnP: Heq_anonymous6 => <-. apply: wordsize_sqrn_div2_gt0.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    rewrite /delete_last -bool_true /blast -!count_delete.
    rewrite /access nth_cat -Heq_l -Heq_r //= -if_neg.
    move/eqP/eqnP/eqP: (H) => ->.
    rewrite addnA subnK; try rewrite addnBA //=;
    rewrite -/access access_leq_count //=.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK. by apply/eqP.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_61, delete_from_leaves_obligation_60 => //=.
    rewrite -Heq_l -Heq_r => //=.
    rewrite /delete_last /blast delete_catR.
    rewrite -cat1s /delete.
    rewrite prednK //= drop_size //= cats0.
    rewrite -cat1s !catA /access //= cats1 -take_nth prednK //= take_size //=.
    rewrite leqNgt. by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP/negbTE: H0 => H0.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /delete_last size_delete //=.
    move: (wildcard'1). rewrite leq_eqVlt H0 //= => H0'.
    by rewrite -(leq_add2r 1) !addn1 prednK.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /delete_last size_delete //=.
    apply: leq_ltn_trans. apply: leq_pred. exact.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    rewrite size_delete. rewrite prednK //=.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
  Qed.

  Next Obligation.
    rewrite size_delete. rewrite prednK //=.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -Heq_anonymous5 /delete_last !size_delete.
    rewrite prednK. rewrite -subn1. by rewrite addnC addnBA //= addnC.
    move/eqP/eqnP: Heq_anonymous6 => <-. apply: wordsize_sqrn_div2_gt0.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK //=. by apply/eqP.
  Qed.

  Next Obligation.
    rewrite /delete_last -bool_true /blast -!count_delete.
    rewrite /access nth_cat -Heq_l -Heq_r //= -if_neg.
    move/eqP/eqnP/eqP: (H) => ->.
    rewrite addnA subnK; try rewrite addnBA //=;
    rewrite -/access access_leq_count //=.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
    rewrite ltn_neqAle leq_pred andbT //= -eqSS prednK. by apply/eqP.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
  Qed.

  Next Obligation.
    have Harr1: 0 < size arr1.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_69, delete_from_leaves_obligation_68 => //=.
    rewrite -Heq_l -Heq_r => //=.
    rewrite /delete_last /blast delete_catR.
    rewrite -cat1s /delete.
    rewrite prednK //= drop_size //= cats0.
    rewrite -cat1s !catA /access //= cats1 -take_nth prednK //= take_size //=.
    rewrite leqNgt. by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    move: (wildcard'3). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H0 => -> //=.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite size_delete //=. apply: leq_ltn_trans.
    apply: leq_pred. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -Heq_anonymous5 size_delete. by rewrite -subn1 addnBA.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    rewrite /access nth_cat -count_delete -Heq_l -Heq_r //= -if_neg.
    move/eqP/eqnP/eqP: (H) => ->.
    rewrite /access addnBA //= -/access access_leq_count //=.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_78, delete_from_leaves_obligation_77 => //=.
    rewrite -Heq_l -Heq_r //= delete_catR //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    move: (wildcard'3). rewrite leq_eqVlt.
    move/eqP/eqnP/eqP/negbTE: H0 => -> //=.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact. 
    rewrite size_delete //=. move => Hw.
    by rewrite -(leq_add2r 1) !addn1 prednK.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite size_delete //=. apply: leq_ltn_trans.
    apply: leq_pred. exact.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    have Harr2: 0 < size arr2.
    apply: leq_trans. apply: wordsize_sqrn_div2_gt0. exact.
    rewrite -Heq_anonymous5 size_delete. by rewrite -subn1 addnBA.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    rewrite /access nth_cat -count_delete -Heq_l -Heq_r //= -if_neg.
    move/eqP/eqnP/eqP: (H) => ->.
    rewrite /access addnBA //= -/access access_leq_count //=.
    rewrite -(ltn_add2l (size arr1)). rewrite subnKC //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_86, delete_from_leaves_obligation_85 => //=.
    rewrite -Heq_l -Heq_r //= delete_catR //= leqNgt.
    by move/eqP/eqnP/eqP: H => ->.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP/ltP/ltP/negbTE: H0 => ->. by rewrite subn0.
  Qed.

  Next Obligation.
    rewrite /access nth_default. rewrite subn0 //=.
    rewrite size_cat -Heq_l -Heq_r //= leqNgt.
    by move/eqP/eqnP/eqP: H0 => ->.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_95, delete_from_leaves_obligation_94 => //=.
    rewrite -Heq_l -Heq_r //= delete_oversize //= leqNgt size_cat.
    by move/eqP/eqnP/eqP: H0 => ->.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP/ltP/ltP/negbTE: H0 => ->. by rewrite subn0.
  Qed.

  Next Obligation.
    rewrite /access nth_default. rewrite subn0 //=.
    rewrite size_cat -Heq_l -Heq_r //= leqNgt.
    by move/eqP/eqnP/eqP: H0 => ->.
  Qed.

  Next Obligation.
    rewrite /eq_rect.
    destruct delete_from_leaves_obligation_103, delete_from_leaves_obligation_102 => //=.
    rewrite -Heq_l -Heq_r //= delete_oversize //= leqNgt size_cat.
    by move/eqP/eqnP/eqP: H0 => ->.
  Qed.    

  Obligation Tactic := idtac.

  (* Here we follow the naming pattern used in Kahrs (2001) *)
  Program Definition balright {lnum rnum lones rones d cl cr}
    (c : color)
    (l : tree lnum lones d cl)
    (r : del_tree rnum rones d cr)
    (ok_l : color_ok c cl)
    (ok_r : color_ok c cr) :
    { B' : del_tree (lnum + rnum) (lones + rones) (incr_black d c) c |
      dflattend B' = dflatten l ++ dflattend r } :=
    match c with
    | Red =>
      match r with
      | Stay _ _ _ _ _ _ r' => Stay Red _ (RNode l r')
      | Down _ _ _ r' =>
        match l with
        | Leaf _ _ _ => _
        | Node _ _ _ _ _ _ clr cl _ _ ll lr =>
          match cl with
          | Red => _
          | Black =>
            match clr with
            | Black => Stay Red _ (BNode ll (RNode lr r'))
            | Red => match lr with
                    | Leaf _ _ _ => _
                    | Node _ _ _ _ _ _ _ _ _ _ lrl lrr =>
                      Stay Red _ (RNode (BNode ll lrl) (BNode lrr r'))
                    end
            end
          end
        end
      end
    | Black =>
      match r with
      | Stay _ _ _ _ _ _ r' => Stay Black _ (BNode l r')
      | Down _ _ _ r' =>
        match l with
        | Leaf _ _ _ => _
        | Node _ _ _ _ _ cll clr cl _ _ ll lr =>
          match clr with
          | Red => match cl with
                  | Red => _
                  | Black =>
                    match lr with
                    | Leaf _ _ _ => _
                    | Node _ _ _ _ _ _ _ _ _ _ lrl lrr =>
                      Stay Black _ (BNode (BNode ll lrl) (BNode lrr r'))
                    end
                  end
          | Black => match cl with
                    | Red =>
                      match cll with
                      | Red => _
                      | Black =>
                        match lr with
                        | Leaf _ _ _ => _
                        | Node _ _ _ _ _ clrl clrr _ _ _ lrl lrr =>
                          match clrr with
                          | Black =>
                            Stay Black _ (BNode ll (BNode lrl (RNode lrr r')))
                          | Red =>
                            match lrr with
                            | Leaf _ _ _ => _
                            | Node _ _ _ _ _ clrrl clrrr _ _ _ lrrl lrrr =>
                              match clrrl with
                              | Red => _
                              | Black =>
                                match clrrr with
                                | Red => _
                                | Black =>
                                  Stay Black _ (BNode ll
                                                 (RNode
                                                    (BNode lrl lrrl)
                                                    (BNode lrrr r')))
                                end
                              end
                            end
                          end
                        end
                      end
                    | Black => Down (BNode ll (RNode lr r'))
                    end
          end
        end
      end
    end.

  Solve All Obligations with (intros; subst; try exact; intuition).

  Next Obligation. intros; subst. by destruct cl. Qed.

  Next Obligation. intros; subst. by destruct cr, wildcard'2. Qed.

  Next Obligation.
    intros; subst.
    rewrite /eq_rect.
    destruct balright_obligation_6, balright_obligation_5 => //=.
    destruct balright_obligation_4, balright_obligation_2 => //=.
    by rewrite -Heq_r.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst.
    rewrite /eq_rect.
    destruct balright_obligation_15, balright_obligation_14.
    destruct balright_obligation_13, balright_obligation_12 => //=.
    by rewrite -Heq_l -Heq_r //= catA.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_24, balright_obligation_23 => //=.
    destruct balright_obligation_22, balright_obligation_20 => //=. 
    by rewrite -Heq_l -Heq_r -Heq_lr //= !catA.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_29, balright_obligation_28 => //=.
    by rewrite -Heq_r.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. rewrite eqSS. by move/eqP => ->.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst => //=. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_40, balright_obligation_39 => //=.
    destruct balright_obligation_38, balright_obligation_36 => //=.
    by rewrite -Heq_l -Heq_r -Heq_lr //= !catA.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.


  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst => //=. move/eqP: Heq_d => //=. by rewrite -eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_50, balright_obligation_49 => //=.
    destruct balright_obligation_48, balright_obligation_46 => //=.
    by rewrite -Heq_l -Heq_r -Heq_lr //= !catA.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst => //=. move/eqP: Heq_d => //=. by rewrite -eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_62, balright_obligation_61.
    destruct balright_obligation_60, balright_obligation_57 => //=.
    by rewrite -Heq_l -Heq_r -Heq_lr -Heq_lrr //= !catA.
  Qed.

  Next Obligation.
    intros; subst. move/eqP: Heq_d => //=. by rewrite eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst => //=. move/eqP: Heq_d => //=. by rewrite -eqSS => /eqP ->.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balright_obligation_68, balright_obligation_66, balright_obligation_65.
    destruct balright_obligation_67 => //=.
    by rewrite -Heq_l -Heq_r //= catA.
  Qed.

 
  Program Definition balleft {lnum rnum lones rones d cl cr}
    (c : color)
    (l : del_tree lnum lones d cl)
    (r : tree rnum rones d cr)
    (ok_l : color_ok c cl)
    (ok_r : color_ok c cr) :
    { B' : del_tree (lnum + rnum) (lones + rones) (incr_black d c) c |
      dflattend B' = dflattend l ++ dflatten r } :=
    match c with
    | Red =>
      match cl with
      | Red => _
      | Black =>
        match cr with
        | Red => _
        | Black =>
          match l with
          | Stay _ _ _ cl' _ _ l' =>
            match cl' with
            | Red => _
            | Black => Stay Red _ (RNode l' r)
            end
          | Down _ _ _ l' =>
            match r with
            | Leaf _ _ _ => _
            | Node _ _ _ _ _ crl crr _ _ _ rl rr =>
              match crl with
              | Red =>
                match rl with
                | Leaf _ _ _ => _
                | Node _ _ _ _ _ crll crlr _ _ _ rll rlr =>
                  match crll with
                  | Red => _
                  | Black =>
                    match crlr with
                    | Red => _
                    | Black => Stay Red _ (RNode (BNode l' rll) (BNode rlr rr))
                    end
                  end
                end
              | Black => Stay Red _ (BNode (RNode l' rl) rr)
              end
            end
          end
        end
      end
    | Black =>
      match l with
      | Stay _ _ _ _ _ _ l' => Stay Black _ (BNode l' r)
      | Down _ _ _ l' =>
        match r with
        | Leaf _ _ _ => _
        | Node _ _ _ _ _ crl crr cr' _ _ rl rr =>
          match crl with
          | Red =>
            match cr' with
            | Red => _
            | Black =>
              match rl with
              | Leaf _ _ _ => _
              | Node _ _ _ _ _ crll crlr _ _ _ rll rlr =>
                match crll with
                | Red => _
                | Black =>
                  match crlr with
                  | Red => _
                  | Black => Stay Black _ (BNode (BNode l' rll) (BNode rlr rr))
                  end
                end
              end
            end
          | Black =>
            match cr' with
            | Red =>
              match crr with
              | Red => _
              | Black =>
                match rl with
                | Leaf _ _ _ => _
                | Node _ _ _ _ _ crll crlr _ _ _ rll rlr =>
                  match crll with
                  | Red =>
                    match rll with
                    | Leaf _ _ _ => _
                    | Node _ _ _ _ _ crlll crllr _ _ _ rlll rllr =>
                      match crlll with
                      | Red => _
                      | Black =>
                        match crllr with
                        | Red => _
                        | Black =>
                          Stay Black _ (BNode (BNode l' rlll)
                                              (RNode (BNode rllr rlr) rr))
                        end
                      end
                    end
                  | Black => Stay Black _ (BNode (BNode (RNode l' rll) rlr) rr)
                  end
                end
              end
            | Black => Down (BNode (RNode l' rl) rr)
            end
          end
        end
      end
    end.

  Solve All Obligations with (intros; subst; try exact; intuition).

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_10, balleft_obligation_9 => //=.
    by rewrite -Heq_l.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_22, balleft_obligation_21.
    destruct balleft_obligation_20, balleft_obligation_17 => //=.
    rewrite /eq_ind_r /eq_ind //=.
    destruct Heq_d. by rewrite -Heq_l -Heq_r //= -Heq_rl //= !catA.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_27, balleft_obligation_29, balleft_obligation_30.
    destruct balleft_obligation_28 => //=.
    rewrite /eq_ind_r /eq_ind => //=.
    destruct Heq_cl. by rewrite -Heq_l -Heq_r //= catA.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_36, balleft_obligation_35, balleft_obligation_34 => //=.
    by rewrite -Heq_l.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_44, balleft_obligation_47, balleft_obligation_48 => //=.
    rewrite /eq_ind_r /eq_ind //=.
    destruct Heq_d. by rewrite -Heq_l -Heq_r //= -Heq_rl //= !catA.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_64, balleft_obligation_63.
    destruct balleft_obligation_62, balleft_obligation_57 => //=.
    rewrite /eq_ind_r /eq_ind //=.
    destruct Heq_d => //=.
    by rewrite -Heq_l -Heq_r //= -Heq_rl //= -Heq_rll //= !catA.
  Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation. intros; subst. by rewrite !addnA. Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_73, balleft_obligation_72.
    destruct balleft_obligation_71, balleft_obligation_67 => //=.
    rewrite /eq_ind_r /eq_ind //=.
    destruct Heq_d. by rewrite -Heq_l -Heq_r //= -Heq_rl //= !catA.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct balleft_obligation_80, balleft_obligation_79.
    destruct balleft_obligation_78, balleft_obligation_75 => //=.
    by rewrite -Heq_l -Heq_r //= catA. 
  Qed.

  Definition pos_black c d :=
    match c with
    | Black => d > 0
    | Red => true
    end.
  
  Program Fixpoint ddelete {num ones d c}
    (B : tree num ones d c)
    (i : nat)
    (H : pos_black c d) { measure (tree_size B) } :
    { B' : del_tree (num - (i < num)) (ones - (daccess B i)) d c |
      dflattend B' = delete (dflatten B) i } :=
    if i < num is true
    then
      match c with
      | Red =>
        match B with
        | Leaf _ _ _ => _
        | Node lnum _ _ _ _ cl cr _ _ _ l r =>
          match cl with
          | Red => _
          | Black =>
            match cr with
            | Red => _
            | Black =>
              if i < lnum is true
              then
                match l with
                | Leaf _ _ _ =>
                  let (res, _) := delete_from_leaves Red l r i in
                  res
                | Node _ _ _ _ _ _ _ _ _ _ ll lr =>
                  let (l', _) := ddelete l i _ in
                  let (res, _) := balleft Red l' r _ _ in
                  res
                end
              else
                match l with
                | Leaf _ _ _ =>
                  let (res, _) := delete_from_leaves Red l r i in
                  res
                | Node _ _ _ _ _ _ _ _ _ _ _ _  =>
                  let (r', _) := ddelete r (i - lnum) _ in
                  let (res, _) := balright Red l r' _ _ in
                  res
                end
            end
          end
        end
      | Black =>
        match B with
        | Leaf arr _ _ => _
        | Node lnum _ _ _ _ cl cr _ _ _ l r =>
          if i < lnum is true
          then
            match r with
            | Leaf _ _ _ =>
              match cl with
              | Black =>
                let (res, _) := delete_from_leaves Black l r i in
                res
              | Red =>
                match l with
                | Leaf _ _ _ => _
                | Node _ _ _ _ _ cll clr _ _ _ ll lr =>
                  match cll with
                  | Red => _
                  | Black =>
                    match clr with
                    | Red => _
                    | Black =>
                      let (lres, _) := delete_from_leaves Red ll lr i in
                      match lres with
                      | Stay _ _ _ _ _ _ lres' =>
                        Stay Black _ (BNode lres' r)
                      | Down _ _ _ _ => _
                      end
                    end
                  end
                end
              end
          | Node _ _ _ _ _ crl crr _ _ _ rl rr =>
            match cr with
            | Red =>
              match crl with
              | Red => _
              | Black =>
                match crr with
                | Red => _
                | Black =>
                  match cl with
                  | Red =>
                    let (l', _) := ddelete l i _ in
                    let (res, _) := balleft Black l' r _ _ in
                    res
                  | Black =>
                    let (l', _) := ddelete (RNode l rl) i _ in
                    let (res, _) := balleft Black l' rr _ _ in
                    res
                  end
                end
              end
            | Black =>
              let (l', _) := ddelete l i _ in
              let (res, _) := balleft Black l' r _ _ in
              res
            end
            end
          else
            match l with
            | Leaf _ _ _ =>
              match cr with
              | Red =>
                match r with
                | Leaf _ _ _ => _
                | Node _ _ _ _ _ crl crr _ _ _ rl rr =>
                  match crl with
                  | Red => _
                  | Black =>
                    match crr with
                    | Red => _
                    | Black =>
                      let (r', _) := delete_from_leaves Red rl rr (i - lnum) in
                      match r' with
                      | Stay _ _ _ _ _ _ r' =>
                        Stay Black _ (BNode l r')
                      | Down _ _ _ _ => _
                      end
                    end
                  end
                end
              | Black =>
                let (res, _) := delete_from_leaves Black l r i in
                res
              end
            | Node llnum _ _ _ _ cll clr _ _ _ ll lr =>
              match cl with
              | Red =>
                match cll with
                | Red => _
                | Black =>
                  match clr with
                  | Red => _
                  | Black =>
                    match cr with
                    | Red =>
                      let (r', _) := ddelete r (i - lnum) _ in
                      let (res, _) := balright Black l r' _ _ in
                      res
                    | Black =>
                      let (r', _) := ddelete (RNode lr r) (i - llnum) _ in
                      let (res, _) := balright Black ll r' _ _ in
                      res
                    end
                  end
                end
              | Black =>
                let (r', _) := ddelete r (i - lnum) _ in
                let (res, _) := balright Black l r' _ _ in
                res
              end
            end
        end
      end
    else Stay c _ B.

  Solve All Obligations with program_simpl.

  Next Obligation.
    intros; subst. subst filtered_var0. by rewrite Heq_anonymous0.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_6, ddelete_func_obligation_5.
    destruct ddelete_func_obligation_7 => //=.
    subst filtered_var. rewrite /access nth_cat //= -Heq_l //=.
    by rewrite -Heq_anonymous. 
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_11, ddelete_func_obligation_10.
    destruct ddelete_func_obligation_9, ddelete_func_obligation_8 => //=.
    move: res H0. rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    by destruct Heq_cl.
  Qed.

  Next Obligation.
    intros; subst. apply/ltP. rewrite -Heq_B -Heq_l //= -[X in X < _]addn0.
    by rewrite -!addnA !ltn_add2l tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var. rewrite -Heq_anonymous //=.
    rewrite [in LHS]addnC -addnA [X in _ = _ + X - _]addnC addnCA addnBA //=.
    by apply: (leq_ltn_trans (n := i)).
  Qed.
      
  Next Obligation.
    intros; subst. subst filtered_var filtered_var0 => //=.
    rewrite -Heq_anonymous [in LHS]addnC -addnA [X in _ = _ + X - _]addnC.
    by rewrite addnCA addnBA //= daccess_leq_ones.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_18, ddelete_func_obligation_17.
    destruct ddelete_func_obligation_20, ddelete_func_obligation_19 => //=.
    subst filtered_var.
    rewrite H1 //= delete_catL. by rewrite H0.
    by rewrite -Heq_l //= size_cat //= !dflatten_sizeK.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var0. by rewrite -Heq_anonymous0.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_24, ddelete_func_obligation_23.
    destruct ddelete_func_obligation_25 => //=.
    subst filtered_var. rewrite -if_neg /access nth_cat -Heq_l //= -if_neg.
    move/eqP/eqnP/eqP: (H0) => ->. by rewrite daccessK /access.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_29, ddelete_func_obligation_28.
    destruct ddelete_func_obligation_27, ddelete_func_obligation_26.
    move: res H1.  rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    by destruct Heq_cl.
  Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    rewrite -Heq_B -Heq_l //= -[X in X < _]add0n.
    by rewrite ltn_add2r ltn_addr //= tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var0 filtered_var.
    have Hi: (i - (wildcard' + wildcard'1) < wildcard'16).
    rewrite -(ltn_add2r (wildcard' + wildcard'1)) subnK.
    by rewrite addnC. move/eqP/eqnP/eqP: (H0). by rewrite -leqNgt.
    by rewrite Hi addnBA //= (leq_ltn_trans (leq0n _) Hi).
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var0 filtered_var => //=.
    rewrite -if_neg. move/eqP/eqnP/eqP: (H0) => H0'.
    rewrite H0' addnBA //= daccess_leq_ones //=.
    rewrite -(ltn_add2r (wildcard' + wildcard'1)) subnK.
    by rewrite addnC. by rewrite leqNgt H0'.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_38, ddelete_func_obligation_37.
    destruct ddelete_func_obligation_36, ddelete_func_obligation_35 => //=.
    rewrite H2. subst filtered_var.
    rewrite delete_catR. by rewrite H1 {2}(dflatten_size l).
    rewrite -(dflatten_size l). move/eqP/eqnP/eqP: H0. by rewrite -leqNgt.
  Qed.

  Next Obligation.
    intros; subst. by subst wildcard'.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var0. by rewrite -Heq_anonymous0.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_43, ddelete_func_obligation_42.
    destruct ddelete_func_obligation_45 => //=.
    subst filtered_var filtered_var0.
    by rewrite daccessK /access nth_cat (dflatten_sizeK l) -Heq_anonymous.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_49, ddelete_func_obligation_48.
    destruct ddelete_func_obligation_47, ddelete_func_obligation_46.
    move: res H0. by rewrite /eq_rect.
  Qed.

  Next Obligation.
    intros; subst.
    subst filtered_var.
    rewrite -Heq_anonymous3 //=.
    rewrite [in LHS]addnC -addnA [X in _ = _ + X - _]addnC addnCA.
    rewrite addnBA //=. by apply: (leq_ltn_trans (n := i)).
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    move: Heq_wildcard'2 lres H0 lres' Heq_lres.
    rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    destruct Heq_wildcard'2 => //= lres H0 lres' Heq_lres.
    rewrite -Heq_anonymous3 -Heq_l //= /access nth_cat dflatten_sizeK.
    case: ifP => Hif;
    rewrite daccessK /access -addnA [in LHS]addnC;
    rewrite [X in _ = _ + X - _]addnC addnCA addnBA //=;
    [ rewrite -{2}(dflatten_countK ll) | rewrite -{2}(dflatten_countK lr) ];
    [ apply: (leq_trans (n := (count_one (dflatten ll)))) | 
      apply: (leq_trans (n := (count_one (dflatten lr)))) ];
    try rewrite -/access access_leq_count //= dflatten_sizeK //=;
    try by rewrite ?leq_addr ?leq_addl.
    rewrite -(ltn_add2r (wildcard'17)) subnK. rewrite addnC //=.
    by rewrite leqNgt Hif.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_63, ddelete_func_obligation_62.
    destruct ddelete_func_obligation_61, ddelete_func_obligation_60 => //=.
    move: Heq_wildcard'2 lres lres' Heq_lres H0.
    rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    destruct Heq_wildcard'2 => lres lres' Heq_lres.
    subst lres => //= ->. rewrite -Heq_l //= [in RHS]delete_catL //=.
    by rewrite size_cat !dflatten_sizeK.
  Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    rewrite -Heq_B -Heq_r //= -[X in X < _]addn0.
    by rewrite ltn_add2l ltn_addr //= tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    rewrite -Heq_anonymous.
    rewrite addnC addnCA (addnC lnum wildcard'1) addnBA //=.
    by rewrite addnA. apply: (leq_ltn_trans (n := i)).
    rewrite leq0n //=. by rewrite -Heq_anonymous.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var => //=.
    rewrite -Heq_anonymous addnC addnCA (addnC wildcard'13 wildcard'2) addnBA //=.
    by rewrite addnA. by rewrite daccess_leq_ones.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect.
    destruct ddelete_func_obligation_75, ddelete_func_obligation_74.
    destruct ddelete_func_obligation_73, ddelete_func_obligation_72 => //=.
    rewrite H1 H0 delete_catL //=. rewrite dflatten_sizeK. by subst filtered_var.
  Qed.

  Next Obligation.
    intros; subst. rewrite /eq_rect //=. apply/ltP.
    rewrite -Heq_B -Heq_r //= -[X in X < _]addn0.
    by rewrite addnA ltn_add2l tree_size_pos. 
  Qed.

  Next Obligation.
    intros; subst.
    subst filtered_var filtered_var0.
    have Hi: i < lnum + wildcard'.
    apply: (leq_trans (n := lnum)) => //=. by rewrite leq_addr.
    rewrite Hi addnC addnBA //=.
    by rewrite addnCA addnA [X in _ = _ + X - _]addnC addnA.
    apply: (leq_ltn_trans (n := i)). by rewrite leq0n. exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    rewrite /eq_rect //= -Heq_anonymous.
    rewrite addnC addnBA //=.
    by rewrite addnCA addnA [X in _ = _ + X - _]addnC addnA.
    rewrite -{2}(dflatten_countK l).
    apply: (leq_trans (n := count_one (dflatten l))).
    by rewrite daccessK access_leq_count //= dflatten_sizeK.
    by rewrite leq_addr.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var. rewrite /eq_rect.
    destruct ddelete_func_obligation_88, ddelete_func_obligation_87.
    destruct ddelete_func_obligation_86, ddelete_func_obligation_85 => //=.
    rewrite H1 H0 /eq_rect //= -Heq_r //=.
    by rewrite !delete_catL ?catA //= dflatten_sizeK.
  Qed.

  Next Obligation. intros; subst. by destruct cl. Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    by rewrite -Heq_B //= -{1}(addn0 (tree_size l)) ltn_add2l tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    rewrite -Heq_anonymous [in LHS]addnC addnBA //=.
    by rewrite [in RHS]addnC. apply: (leq_ltn_trans (n := i)).
    by rewrite leq0n. exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var => //=.
    rewrite -Heq_anonymous.
    rewrite addnC addnBA //=.
    by rewrite addnCA [X in _ = _ + X - _]addnC addnA.
    rewrite -{2}(dflatten_countK l).
    apply: (leq_trans (n := count_one (dflatten l))).
    by rewrite daccessK access_leq_count //= dflatten_sizeK.
    by rewrite leqnn.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var. rewrite /eq_rect.
    destruct ddelete_func_obligation_97, ddelete_func_obligation_96.
    destruct ddelete_func_obligation_95, ddelete_func_obligation_94 => //=.
    by rewrite H1 H0 delete_catL //= dflatten_sizeK -Heq_anonymous.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    have Hi: (i - size wildcard'10 < wildcard'18 + wildcard'20).
    rewrite -(ltn_add2r (size wildcard'10)) subnK //=.
    by rewrite addnC -Heq_anonymous4.
    move/eqP/eqnP/eqP: (H0). by rewrite -leqNgt.  
    rewrite Hi addnBA //=. apply: (leq_ltn_trans (n := i - size wildcard'10)).
    by rewrite leq0n. exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_103, ddelete_func_obligation_102.
    destruct ddelete_func_obligation_105 => //=.
    move/eqP/eqnP/eqP: (H0) => H0'. rewrite -if_neg H0' //=.
    rewrite daccessK. move: Heq_r r'0 H1 r' Heq_r'.
    rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    destruct Heq_wildcard'2 => //= Heq_r r'0 H1 r' Heq_r'.
    rewrite -Heq_r //= addnA addnBA //=. rewrite addnA //=.
    rewrite -{2}(dflatten_countK rl) -{2}(dflatten_countK rr).
    have Hcount: (count_one (dflatten rl) + count_one (dflatten rr) = count_one (dflatten rl ++ dflatten rr)).
    by rewrite /count_one count_cat.
    rewrite Hcount access_leq_count //=.
    rewrite size_cat !dflatten_sizeK -(ltn_add2r (size wildcard'10)) subnK //=.
    by rewrite addnC -Heq_anonymous4. move/eqP/eqnP/eqP: (H0).
    by rewrite leqNgt.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_111, ddelete_func_obligation_110.
    destruct ddelete_func_obligation_109, ddelete_func_obligation_108 => //=.
    move: Heq_r r'0 H1 r' Heq_r'.
    rewrite /eq_rect //= /eq_ind_r /eq_ind //=.
    destruct Heq_wildcard'2 => //= Heq_r r'0 H1 r' Heq_r'.
    move: H1. rewrite -Heq_r -Heq_r' //= => ->.
    rewrite [in RHS]delete_catR. by rewrite dflatten_sizeK.
    rewrite leqNgt dflatten_sizeK. by move/eqP/eqnP/eqP: H0.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    by rewrite -Heq_anonymous0.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_116, ddelete_func_obligation_115 => //=.
    move/eqP/eqnP/eqP: (H0) => H0'. rewrite -if_neg H0' daccessK /access.
    by rewrite nth_cat dflatten_sizeK -if_neg H0'.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_121, ddelete_func_obligation_120.
    by destruct ddelete_func_obligation_119, ddelete_func_obligation_118.
  Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    by rewrite -Heq_B //= -{1}(add0n (tree_size r)) ltn_add2r tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    have Hi: i - (llnum + wildcard'0) < wildcard'8.
    rewrite -(ltn_add2r (llnum + wildcard'0)) subnK //=.
    by rewrite addnC -Heq_anonymous0.
    move/eqP/eqnP/eqP: (H0) => H0'. by rewrite leqNgt H0'.
    rewrite Hi addnBA //=. apply: (leq_ltn_trans (n := (i - (llnum + wildcard'0)))).
    by rewrite leq0n. exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0 => //=.
    move/eqP/eqnP/eqP: (H0) => H0'. rewrite -if_neg H0'.
    rewrite addnBA //= -{2}(dflatten_countK r) daccessK access_leq_count //=. 
    rewrite dflatten_sizeK. rewrite -(ltn_add2r (llnum + wildcard'0)) subnK //=.
    by rewrite addnC -Heq_anonymous0. by rewrite leqNgt H0'.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_132, ddelete_func_obligation_131.
    destruct ddelete_func_obligation_130, ddelete_func_obligation_129 => //=.
    rewrite H2 H1 delete_catR dflatten_sizeK //= leqNgt.
    by move/eqP/eqnP/eqP: (H0) => ->.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    rewrite /eq_rect //=. apply/ltP.
    rewrite -Heq_B -Heq_l //= -(add0n (tree_size lr + tree_size r)).
    by rewrite -addnA ltn_add2r tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    have Hi: i - llnum < wildcard'0 + wildcard'8.
    rewrite -(ltn_add2r llnum) subnK. by rewrite addnC addnA -Heq_anonymous0.
    apply: (leq_trans (n := llnum + wildcard'0)). by rewrite leq_addr.
    rewrite leqNgt. by move/eqP/eqnP/eqP: (H0) => ->.
    rewrite Hi addnBA //=. by rewrite addnA.
    apply: (leq_ltn_trans (n := (i - llnum))). by rewrite leq0n.
    exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect //=.
    move/eqP/eqnP/eqP: (H0) => H0'.
    have leq_llnum_i: (llnum <= i).
    apply: (leq_trans (n := llnum + wildcard'0)).
    by rewrite leq_addr. by rewrite leqNgt H0'.
    have Hi: i - llnum >= wildcard'0. rewrite -(leq_add2r llnum) subnK.
    by rewrite addnC leqNgt H0'. apply: (leq_trans (n := (llnum + wildcard'0))).
    by rewrite leq_addr. by rewrite leqNgt.  
    rewrite -if_neg -leqNgt -[in RHS]if_neg H0' Hi addnBA. rewrite addnA.
    have Hi': (i - llnum - wildcard'0 == i - (llnum + wildcard'0)).
    rewrite -(eqn_add2r wildcard'0) subnK //= -(eqn_add2r llnum) subnK //=.
    rewrite -addnA [X in _ == _ - X + _]addnC subnK //=.
    by rewrite leqNgt addnC H0'.  
    by rewrite (eqP Hi'). rewrite -{2}(dflatten_countK r).
    apply: (leq_trans (n := count_one (dflatten r))).
    rewrite dflatten_countK daccess_leq_ones //=.
    rewrite -(ltn_add2r wildcard'0) subnK //= -(ltn_add2r llnum) subnK //=.
    by rewrite addnC [X in _ < _ + X]addnC addnA. by rewrite leq_addl.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_144, ddelete_func_obligation_143.
    destruct ddelete_func_obligation_142, ddelete_func_obligation_141.
    rewrite H2 H1 //= -Heq_l //= -[in RHS]catA [in RHS]delete_catR.
    by rewrite dflatten_sizeK.
    rewrite dflatten_sizeK. apply: (leq_trans (n := llnum + wildcard'0)).
    by rewrite leq_addr. move/eqP/eqnP/eqP: (H0) => H0'. by rewrite leqNgt H0'.
  Qed.

  Next Obligation. intros; subst. by destruct cr. Qed.

  Next Obligation.
    intros; subst. apply/ltP.
    by rewrite -Heq_B //= -{1}(add0n (tree_size r)) ltn_add2r tree_size_pos.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0.
    have Hi: i - (llnum + wildcard'0) < wildcard'8.
    rewrite -(ltn_add2r (llnum + wildcard'0)) subnK //=.
    by rewrite addnC -Heq_anonymous0. rewrite leqNgt. by move/eqP/eqnP/eqP: (H0).
    rewrite Hi addnBA //=.
    apply: (leq_ltn_trans (n := (i - (llnum + wildcard'0)))).
    by rewrite leq0n. exact.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0 => //=.
    move/eqP/eqnP/eqP: (H0) => H0'. rewrite -if_neg H0'.
    rewrite addnBA //= -{2}(dflatten_countK r) daccessK access_leq_count //=. 
    rewrite dflatten_sizeK. rewrite -(ltn_add2r (llnum + wildcard'0)) subnK //=.
    by rewrite addnC -Heq_anonymous0. by rewrite leqNgt H0'.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var filtered_var0. rewrite /eq_rect.
    destruct ddelete_func_obligation_153, ddelete_func_obligation_152.
    destruct ddelete_func_obligation_151, ddelete_func_obligation_150 => //=.
    rewrite H2 H1 delete_catR dflatten_sizeK //= leqNgt.
    by move/eqP/eqnP/eqP: (H0) => ->.
  Qed.

  Next Obligation. intros; subst. by subst wildcard'. Qed.

  Next Obligation. intros; subst. by destruct c. Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    move/eqP/eqnP/eqP/ltP/ltP/negbTE: H0 => -> //=.
    by rewrite subn0.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var.
    rewrite daccessK /access nth_default //=. by rewrite subn0.
    rewrite dflatten_sizeK leqNgt. by move/eqP/eqnP/eqP: H0.
  Qed.

  Next Obligation.
    intros; subst. subst filtered_var. rewrite /eq_rect.
    destruct ddelete_func_obligation_158, ddelete_func_obligation_157 => //=.
    rewrite delete_oversize //= dflatten_sizeK leqNgt. by move/eqP/eqnP/eqP: H0.
  Qed.

  Next Obligation. intros; subst. by subst wildcard'. Qed.
  
End delete.

End dynamic_dependent.