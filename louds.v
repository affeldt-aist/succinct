From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select pred_succ.

(** * A formalization of LOUDS trees *)

(* OUTLINE:
  0. Section louds_encoding
  1. Section size_louds
  followed by Sections on the operations listed in todo.org
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section louds_encoding.

Variable A : Type.
Implicit Types l : forest A.

Definition node_description l := rcons (nseq (size l) true) false.

Lemma size_node_description l : size (node_description l) = (size l).+1.
Proof. by rewrite size_rcons size_nseq. Qed.

Lemma count_mem_false_node_description l :
  count_mem false (node_description l) = 1.
Proof.
rewrite /node_description -cats1 count_cat addn1; congr S.
apply/count_memPn/nseqP; by case.
Qed.

Lemma count_mem_true_node_description l :
  count_mem true (node_description l) = size l.
Proof.
rewrite /node_description -cats1 count_cat addn0; apply/eqP.
by rewrite -[X in _ == X](size_nseq _ true) -all_count all_nseq orbT.
Qed.

Definition LOUDS (t : tree A) :=
  [:: true, false & lo_traversal node_description t].

End louds_encoding.

Section size_louds.

Lemma size_seq_of_tree (A : eqType) (t : tree A) :
  size (seq_of_tree (@node_description A) t) = (number_of_nodes t).*2.-1.
Proof.
elim/tree_ind3 : t => h l IH /=.
rewrite size_cat size_node_description addSn !size_flatten; congr S.
rewrite (_ : _ (shape _) = sumn (map (fun x => (number_of_nodes x).*2.-1) l)); last first.
  rewrite /shape -map_comp;congr sumn; by apply eq_in_map => t /IH.
rewrite /shape -map_comp !sumnE !big_map -doubleE -sum1_size -big_split /=.
rewrite -muln2 big_distrl /=; apply eq_bigr => t _; rewrite add1n muln2.
by rewrite prednK // double_gt0 number_of_nodes_gt0.
Qed.

Lemma size_level_order_traversal'_nil (A B : Type) n (f : forest A -> seq B) :
  lo_traversal' f n [::] = [::].
Proof. by elim: n. Qed.

Lemma number_of_nodes_children (A : Type) (t : tree A) :
  (number_of_nodes t).*2.-1 =
  1 + size (children_of_node t) +
  \sum_(t' <- children_of_node t) (number_of_nodes t').*2.-1.
Proof.
rewrite /number_of_nodes.
case: t => [v l] => /=.
rewrite -doubleE -addnA add1n.
f_equal.
rewrite size_flatten /shape sumnE !big_map.
rewrite -sum1_size -big_split /=.
rewrite -muln2 big_distrl /=.
apply eq_bigr => i _.
by rewrite muln2 add1n prednK // double_gt0 number_of_nodes_gt0.
Qed.

Variable A : eqType.

Lemma size_level_order_traversal' n (l : forest A) :
  all (fun x => n >= height x) l ->
  size (lo_traversal' (@node_description A) n l) =
    \sum_(t <- l) (number_of_nodes t).*2.-1.
Proof.
elim: n l => [|].
  case => //=.
    by rewrite big_nil.
  move=> h d.
  by rewrite leqNgt height_gt0.
move=> n IH l H.
rewrite /= size_cat IH; last first.
  apply/allP => t.
  case/flatten_mapP => -[v l'] Hv Ht.
  move/allP : H.
  move/(_ _ Hv)/height_Node; by apply.
evar (f : tree A -> nat).
rewrite [RHS](eq_bigr f); last first.
  move=> i _; exact: number_of_nodes_children.
subst f => /=.
rewrite big_split /= big_flatten /=.
f_equal.
  rewrite size_flatten sumnE !big_map.
  apply eq_bigr => -[v l'] _ /=.
  by rewrite size_node_description add1n.
rewrite big_map.
by apply eq_bigr => -[v l'] _.
Qed.

Lemma size_level_order_traversal (t : tree A) :
  size (lo_traversal (@node_description A) t) =
  (number_of_nodes t).*2.-1.
Proof.
rewrite /lo_traversal.
move: (all_seq1 (fun x => height t >= height x) t); rewrite leqnn.
move/size_level_order_traversal' => ->.
by rewrite big_cons big_nil addn0.
Qed.

Lemma size_LOUDS (t : tree A) : size (LOUDS t) = (number_of_nodes t).*2.+1.
Proof.
rewrite /= size_level_order_traversal /=.
by rewrite prednK // double_gt0 number_of_nodes_gt0.
Qed.

End size_louds.

Section nodemap.

Variable A : Type.

(* see [Navarro, p.214] *)
Definition nodemap (T : tree A) (v (*position in the bitstring*): nat) : nat :=
  rank false v.-1 (LOUDS T) (*label*).

Lemma position_2_is_root (T : tree A) : nodemap T 2 = O (*label of root*).
Proof. by rewrite /nodemap /= /LOUDS rank_cons add0n rank0. Qed.

End nodemap.

Section nodeselect.

Variable A : Type.

(* see [Navarro, p.214] *)
Definition nodeselect (T : tree A) i(*label*) : nat :=
  select false i.+1 (LOUDS T) (*position in the bitstring*).

Lemma root_is_at_2 T : nodeselect T 0 = 2.
Proof. by rewrite /nodeselect /= select0. Qed.

End nodeselect.

Require Import Wf_nat.

Section position.

Variable A : eqType.

(* the tth child node v, see [Navarro, p.215] *)
Definition LOUDS_child (B : bitseq) (v t : nat) :=
  select false (rank true (v + t) B).+1 B.

Definition LOUDS_subtree (B : bitseq) (p : seq nat) :=
  foldl (LOUDS_child B) 2 p.

Section lo_traversal.
Variable B : Type.
Variable f : tree A -> B.

Fixpoint lo_traversal_lt (wood : forest A) (p : seq nat) : seq B :=
  match p, wood with
  | nil, _ => nil
  | _, nil => nil
  | n :: p', t :: wood' =>
    let: Node _ cl := t in
    map f wood ++ map f (take n cl)
        ++ lo_traversal_lt (drop n cl ++
                                 children_of_forest (wood' ++ take n cl)) p'
  end.

Fixpoint lo_traversal_res (wood : forest A) (p : seq nat) : forest A :=
  match p, wood with
  | nil, _ => wood
  | _, nil => nil
  | n :: p', t :: wood' =>
    let: Node _ cl := t in
    lo_traversal_res (drop n cl ++ children_of_forest (wood' ++ take n cl)) p'
  end.

Lemma lo_traversal_lt_cat wood p1 p2 :
  lo_traversal_lt wood (p1 ++ p2) =
  lo_traversal_lt wood p1 ++ lo_traversal_lt (lo_traversal_res wood p1) p2.
Proof.
elim: p1 wood => //= n l IH [|[a cl] wood].
  by case: p2 {IH}.
by rewrite IH !catA.
Qed.

Lemma lo_traversal_lt_cons wood n p :
  lo_traversal_lt wood (n :: p) =
  lo_traversal_lt wood [:: n]
                  ++ lo_traversal_lt (lo_traversal_res wood [:: n]) p.
Proof. exact (lo_traversal_lt_cat wood [:: n] p). Qed.

End lo_traversal.

Variable dA : A.
Notation dummy := (Node dA [::]).

Lemma size_lo_traversal w p :
  valid_position (Node dA w) (0 :: p) ->
  size (lo_traversal_res w p) > 0.
Proof.
elim: p w => [|n p IH] [|[a cl] w] //= /andP [Hn HV].
rewrite IH //.
rewrite /= size_cat ltn_addr /=; last by rewrite size_drop ltn_subRL addn0.
case Hd: (drop n cl).
  move: (f_equal size Hd).
  rewrite size_drop /= => /eqP.
  by rewrite subn_eq0 leqNgt Hn.
move: HV.
by rewrite -(addn0 n) -nth_drop Hd.
Qed.

Definition LOUDS_lt w p :=
  flatten (lo_traversal_lt (fun t => node_description (children_of_node t))
                           w p).

Eval compute in LOUDS_lt
  [:: Node dA [:: Node dA [:: Node dA [::]]; Node dA [::]]] (0::0::0::nil).

Eval compute in LOUDS_lt
  [:: Node dA [:: Node dA [:: Node dA [::]]; Node dA [::]]] (0::nil).

Eval compute in LOUDS_lt
  [:: Node dA [:: Node dA [:: Node dA [::]]; Node dA [::]]] (0::1::nil).

Eval compute in LOUDS_lt
  [:: Node dA [:: Node dA [:: Node dA [::]]; Node dA [::]]] (1::nil).

Definition LOUDS_position w p := size (LOUDS_lt w p).

Definition LOUDS_index w p := size (lo_traversal_lt id w p).

Eval compute in LOUDS_index
  [:: Node dA [:: Node dA [:: Node dA [::]]; Node dA [::]]] (1::nil).

Lemma LOUDS_lt_cons w n p :
  LOUDS_lt w (n :: p) =
  LOUDS_lt w [:: n] ++ LOUDS_lt (lo_traversal_res w [:: n]) p.
Proof. by rewrite /LOUDS_lt lo_traversal_lt_cons flatten_cat. Qed.

Lemma LOUDS_lt_cat w p1 p2 :
  LOUDS_lt w (p1 ++ p2) =
  LOUDS_lt w p1 ++ LOUDS_lt (lo_traversal_res w p1) p2.
Proof. by rewrite /LOUDS_lt lo_traversal_lt_cat flatten_cat. Qed.

Lemma LOUDS_position_cons w n p :
  LOUDS_position w (n :: p) =
  LOUDS_position w [:: n] + LOUDS_position (lo_traversal_res w [:: n]) p.
Proof. by rewrite /LOUDS_position LOUDS_lt_cons size_cat. Qed.

Lemma nth_head_drop (T : eqType) (dT : T) n s :
  nth dT s n = head dT (drop n s).
Proof. by rewrite -{1}(addn0 n) -nth_drop nth0. Qed.

Lemma select_false_node_description (l : forest A) :
  select false 1 (node_description l) = (size l).+1.
Proof. rewrite /node_description; elim: l => //= a l IH; by rewrite IH. Qed.

(* not used *)
Lemma select_true_node_description (l : forest A) i : i <= size l ->
  select true i (node_description l) = i.
Proof.
rewrite /node_description; elim: l i => //= [|a l IH] [|i] //.
by rewrite ltnS => /IH ->.
Qed.

Lemma rank_true_node_description (l : forest A) i : i <= size l ->
  rank true i (node_description l) = i.
Proof.
rewrite /node_description; elim: l i => //= [|a l IH] [|i] //.
by rewrite ltnS rank_cons => /IH ->.
Qed.

Lemma count_mem_false_flatten_node_description (l : seq (forest A)) :
  count_mem false (flatten [seq node_description i | i <- l]) = size l.
Proof.
rewrite count_flatten -map_comp sumnE big_map -sum1_size.
apply eq_bigr => i _ /=.
by rewrite count_mem_false_node_description.
Qed.

Lemma select_false_children_of_forest (l : forest A) a : a <= size l ->
  select false a
    (flatten [seq node_description i | i <- children_of_forest' l]) =
  a + size (children_of_forest (take a l)).
Proof.
elim: a l => [|a IH] [|t l] //= Hl; first by rewrite select0.
rewrite children_of_forest_cons size_cat addSn addnCA -addSn select_cat.
rewrite count_mem_false_node_description size_node_description.
case: ifP => Ha.
  destruct a => //; by rewrite take0 /= !addn0 select_false_node_description.
by rewrite subn1 /= IH.
Qed.

Lemma size_flatten_node_description (l : forest A) :
  size (flatten [seq node_description i | i <- children_of_forest' l]) =
  size l + size (children_of_forest l).
Proof.
elim: l => //= t f IH; rewrite children_of_forest_cons [in RHS]size_cat.
by rewrite addSn addnCA -IH size_cat size_node_description addSn.
Qed.

Lemma valid_position_drop a cl n p w :
  valid_position (Node a cl) (n :: p) ->
  valid_position (head dummy (drop n cl ++ w)) p.
Proof.
rewrite -nth0 nth_cat size_drop ltn_subRL addn0 => /= /andP [Hn].
by rewrite Hn (set_nth_default dummy) // nth_head_drop.
Qed.

Lemma LOUDS_position_select w p p' :
  valid_position (head dummy w) p ->
  LOUDS_position w p = select false (LOUDS_index w p) (LOUDS_lt w (p ++ p')).
Proof.
rewrite /LOUDS_position /LOUDS_lt.
elim: p w => // [|n p IH].
  move=> [|? ?]; by rewrite /LOUDS_index /= select0.
move=> [|[a cl] w] HV //=.
rewrite !catA -map_cat map_comp -/(children_of_forest' (w ++ take n cl)).
rewrite /LOUDS_index /= !size_cat size_node_description !size_map.
rewrite -(add1n (size w + _)) select_addn.
rewrite count_cat count_mem_false_node_description /=.
rewrite select_cat count_mem_false_node_description /=.
rewrite select_false_node_description.
congr addn.
rewrite drop_size_cat; last by rewrite size_node_description.
rewrite addnA flatten_cat size_cat.
rewrite IH; last by rewrite (valid_position_drop _ HV).
rewrite flatten_cat select_addn count_cat.
rewrite count_mem_false_flatten_node_description size_map (size_cat w) leq_addr.
rewrite select_cat count_mem_false_flatten_node_description.
rewrite size_map (size_cat w) leqnn.
rewrite select_false_children_of_forest; last by rewrite size_cat leqnn.
rewrite size_flatten_node_description size_cat.
congr addn.
  by rewrite -size_cat take_size.
rewrite drop_size_cat // size_flatten_node_description.
by rewrite -(size_cat w) take_size.
Qed.

Theorem LOUDS_index_rank w p n :
  valid_position (head dummy w) (rcons p n) ->
  LOUDS_index w (rcons p n) =
  size w + rank true (LOUDS_position w p + n) (LOUDS_lt w (rcons p n)).
Proof.
rewrite /LOUDS_position /LOUDS_lt /LOUDS_index.
elim: p w => [|i p IH] [|[a cl] w] HV //=.
  move: HV => /= /andP [Hi _].
  rewrite size_cat !cats0 add0n /= !size_map -addSn size_take Hi.
  rewrite rank_cat size_node_description ltnS (ltnW Hi).
  by rewrite rank_true_node_description // ltnW.
rewrite !catA -!map_cat map_comp -/(children_of_forest' (w ++ take i cl)).
rewrite !size_cat !size_map size_cat -addnA -addSn.
congr addn.
rewrite -addnA rank_addn rank_cat ltnn rank_size //.
rewrite count_mem_true_node_description subnn rank0 addn0 drop_cat ltnn.
rewrite subnn drop0.
rewrite IH; last by rewrite (valid_position_drop _ HV).
rewrite {IH} size_cat !addnA -size_cat cat_take_drop -addnA.
congr addn.
rewrite flatten_cat size_cat -addnA [in RHS]rank_addn flatten_cat.
congr addn.
  rewrite rank_cat ltnn subnn rank0 addn0 [in RHS]rank_size //.
  rewrite count_flatten -map_comp sumnE big_map.
  rewrite size_flatten sumnE big_map; apply eq_bigr => t _ /=.
  by rewrite count_mem_true_node_description.
congr rank.
by rewrite drop_cat ltnn subnn drop0.
Qed.

Theorem LOUDS_childE (t : tree A) (p : seq nat) x :
  let B := LOUDS_lt [::t] (rcons p x) in
  valid_position t (rcons p x) ->
  LOUDS_child B (LOUDS_position [:: t] p) x = LOUDS_position [:: t] (rcons p x).
Proof.
rewrite /LOUDS_child => HV.
rewrite -add1n (_ : 1 = size [::t]) // -LOUDS_index_rank //.
by rewrite (@LOUDS_position_select _ _ [::]) ?cats0.
Qed.

Lemma rankK b n B : nth (negb b) B n = b -> select b (rank b n B).+1 B = n.+1.
Proof.
elim: n B => [|n IH] [|a B] //= Hn.
+ by rewrite rank0 Hn eqxx select0.
+ by destruct b.
+ rewrite rank_cons.
  case: (a == b) => /=.
    by rewrite IH.
  by rewrite -[in RHS](IH _ Hn).
Qed.

Lemma take_children_position t p x :
  valid_position t p ->
  take (children t p).+1 (drop (LOUDS_position [:: t] p)
                               (LOUDS_lt [:: t] (rcons p x)))
  = node_description (children_of_node (subtree t p)).
Proof.
move=> HV.
rewrite /LOUDS_position -cats1 LOUDS_lt_cat drop_cat ltnn subnn drop0.
set w := [:: t].
rewrite (_ : t = head dummy w) // in HV *.
have Hw: size w > 0 by [].
elim: p w Hw HV => [|n p IH] [|[a cl] w] //= Hw.
  rewrite /LOUDS_lt /children /= take_cat size_node_description ltnS ltnn.
  by rewrite subnn take0 cats0.
move=> /andP [Hn].
set w' := drop n cl ++ _.
rewrite /children /= (set_nth_default dummy _ Hn) nth_head_drop.
rewrite (_ : head dummy (drop n cl) = head dummy w').
  move/IH => -> //.
  by rewrite size_cat size_drop ltn_addr // ltn_subRL addn0.
by rewrite -!nth0 /w' nth_cat size_drop ltn_subRL addn0 Hn.
Qed.

Lemma rank_false_LOUDS_position t p x :
  valid_position t (rcons p x) ->
  rank false x.+1 (drop (LOUDS_position [:: t] p)
                        (LOUDS_lt [:: t] (rcons p x))) = 0.
Proof.
move => HV.
rewrite -(cat_take_drop (children t p).+1 (drop _ _)).
rewrite take_children_position ?(valid_position_rcons HV) //.
rewrite /rank /node_description -cats1 -catA takel_cat.
  by apply /count_memPn /negP => /mem_take /nseqP /andP.
by rewrite size_nseq valid_position_children. 
Qed.

Lemma LOUDS_index_leq_count_mem_false t p x :
  LOUDS_index [:: t] (rcons p x) <=
  (count_mem false) (LOUDS_lt [:: t] (rcons p x)).
Proof.
rewrite /LOUDS_index /LOUDS_lt.
elim: {p} (rcons p x) [:: t] => // n p IH [|[a cl] w] //=.
rewrite !catA -!map_cat size_cat size_map.
rewrite count_cat count_mem_false_node_description.
rewrite flatten_cat count_cat map_comp.
rewrite count_mem_false_flatten_node_description size_map add1n ltnS.
by rewrite leq_add2l.
Qed.

Lemma nth_LOUDS_position t p x :
  valid_position t (rcons p x) ->
  nth false (LOUDS_lt [:: t] (rcons p x)) (LOUDS_position [:: t] p + x) = true.
Proof.
move=> HV; move/rank_false_LOUDS_position: (HV).
rewrite /rank -nth_drop => /count_memPn.
case Hx: (nth _ _ _) => //.
rewrite (take_nth (~~ true)).
  by rewrite mem_rcons in_cons Hx eqxx.
move/take_children_position/(f_equal size): (valid_position_rcons HV).
move/(_ x); rewrite size_take.
case: ifP => Hc Hc'.
  rewrite (leq_trans _ Hc) //.
  by rewrite ltnW // ltnS ltnW // ltnS valid_position_children.
rewrite Hc' size_rcons size_nseq.
by rewrite ltnW // ltnS valid_position_children.
Qed.

Lemma rank_false_last_LOUDS_position w n sz :
  sz.+1 = LOUDS_position w [:: n] ->
  rank false 1 (drop sz (LOUDS_lt w [:: n])) = 1.
Proof.
rewrite /LOUDS_position /LOUDS_lt /=.
case: w => // [[a cl] w].
rewrite cats0 -map_cat.
elim/last_ind: ((_ :: w) ++ _) => // a' cl' _.
rewrite map_rcons -cats1 flatten_cat size_cat /= cats0.
rewrite size_node_description !addnS => -[] ->.
rewrite drop_cat ltnNge leq_addr /= addKn /node_description.
rewrite drop_rcons; last by rewrite size_nseq.
rewrite -{1}(size_nseq (size (children_of_node cl')) true).
by rewrite drop_size /= rank_cons eqxx rank0.
Qed.

Lemma pred_false_LOUDS_position t p x :
  valid_position t (rcons p x) ->
  pred false (LOUDS_lt [:: t] (rcons p x)) (LOUDS_position [:: t] p) =
  LOUDS_position [:: t] p.
Proof.
move/valid_position_rcons.
rewrite /LOUDS_position -cats1 LOUDS_lt_cat.
remember (size _) as sz.
case /boolP: (sz == 0) => Hsz HV.
  by rewrite (eqP Hsz) /pred rank0 select0.
destruct sz => //.
rewrite pred_is_self //.
set w := [:: t] in Heqsz *.
rewrite (_ : t = head dummy w) // in HV.
elim: p {t} w sz (LOUDS_lt _ [:: x]) HV Heqsz {Hsz} => // n p IH w sz B HV.
rewrite LOUDS_lt_cons size_cat -catA.
case Hp: (size (LOUDS_lt _ p)).
  rewrite addn0 => Hsz.
  rewrite drop_cat Hsz leqnn rank_cat size_drop -Hsz -(add1n sz) addnK ltnn.
  by rewrite subnn rank0 addn0 rank_false_last_LOUDS_position.
rewrite addnS => -[Hsz].
rewrite drop_cat Hsz leqNgt ltnS leq_addr addKn IH //.
destruct w as [|[a cl] w] => //=.
by rewrite (valid_position_drop _ HV).
Qed.

Definition LOUDS_parent (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v B) B in
  pred false B j.

Theorem LOUDS_parentE (t : tree A) p x :
  valid_position t (rcons p x) ->
  LOUDS_parent (LOUDS_lt [:: t] (rcons p x))
               (LOUDS_position [:: t] (rcons p x)) =
  LOUDS_position [:: t] p.
Proof.
rewrite /LOUDS_parent => HV.
rewrite (LOUDS_position_select [::]) // cats0.
rewrite selectK; last by apply LOUDS_index_leq_count_mem_false.
rewrite LOUDS_index_rank // add1n.
rewrite rankK; last by apply nth_LOUDS_position.
rewrite -addnS pred_same_of_rank; last by apply rank_false_LOUDS_position.
by apply pred_false_LOUDS_position.
Qed.

(* see [Navarro, p.214, l.-1] *)
Definition LOUDS_children (B : bitseq) (v : nat) : nat :=
  succ false B v.+1 - v.+1.

(* TODO: prove that LOUDS_children coincides with children (the definition using trees) *)
Theorem LOUDS_childrenE (t : tree A) (p : seq nat) :
  let B := LOUDS_lt [:: t] (rcons p 0) in
  valid_position t p ->
  children t p = LOUDS_children B (LOUDS_position [:: t] p).
Proof.
move=> B HV.
rewrite /LOUDS_children succ_drop; last first.
  rewrite /LOUDS_position /B.
  rewrite -cats1 LOUDS_lt_cat.
  rewrite size_cat -[X in X < _]addn0 ltn_add2l.
  move: (@size_lo_traversal [:: t] _ HV).
  case: (lo_traversal_res _ _) => //= [[a cl] w] _.
  rewrite /LOUDS_lt /=.
  by rewrite size_cat size_node_description addSn.
rewrite -(cat_take_drop (children t p).+1 (drop _ _)).
rewrite take_children_position //.
rewrite select_cat count_mem_false_node_description /=.
by rewrite select_false_node_description.
Qed.

Definition LOUDS_childrank (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v.-1 B) B in
  j - pred false B j.

End position.
