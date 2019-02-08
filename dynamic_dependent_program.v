From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program.
Require Import set_clear Wf_nat Compare_dec ExtrOcamlNatInt.

Tactic Notation "remember_eq" constr(expr) ident(vname) ident(eqname) := case (exist (fun x => x = expr) expr erefl) => vname eqname.

Section dynamic_dependent.

Variable w : nat.
Hypothesis wordsize_gt1: w > 1.

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

  Definition count_one arr := count_mem true arr.

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
  Qed. Check @Leaf.

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

 Check Node.

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