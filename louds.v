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

Section child.

Variable A : eqType.

(* the tth child node v, see [Navarro, p.215] *)
Definition LOUDS_child (B : bitseq) (v t : nat) :=
  select false (rank true (v + t) B).+1 B.

Definition LOUDS_subtree (B : bitseq) (p : seq nat) :=
  foldl (LOUDS_child B) 2 p.

(*
Theorem LOUDS_node (t : tree A) (p : seq nat) :
  let B := LOUDS t in
  valid_position t p ->
  take (children t p).+1 (drop (LOUDS_subtree B p) B) =
  node_description (children_of_node (subtree t p)).
Proof.
move=> B.
remember (size p) as n.
elim/lt_wf_ind: n p Heqn => n IH.
elim/last_ind => [_ _|p x _].
  rewrite /LOUDS_subtree /children.
  destruct t => /=.
  rewrite /level_order_children_traversal /level_order_children_traversal' /=.
Abort.
*)

(*
Fixpoint lex_order (p1 p2 : seq nat) :=
  match p1, p2 with
  | [::], _ => true
  | a :: p'1, b :: p'2 => (a < b) || (a == b) && lex_order p'1 p'2
  | _, _ => false
  end.

Definition level_order (p1 p2 : seq nat) :=
  (size p1 < size p2) || (size p1 == size p2) && lex_order p1 p2.

Fixpoint count_nodes (f : seq (tree A)) (depth : nat) :=
  if depth is d.+1 then
    sumn [seq 1 + count_nodes (children_of_node c) d | c <- f]
  else 0.

Fixpoint count_smaller (t : tree A) (p : seq nat) :=
  match p with
  | [::] => 0
  | a :: p =>
    let cl := children_of_node t in
    count_nodes (take a cl) (size p).+1 +
    (*if a < size cl then*) 1 + count_smaller (nth t cl a) p
    + count_nodes (drop a.+1 cl) (size p)
  end.
*)

Fixpoint count_smaller_fix (left right : forest A) (p : seq nat) :=
  match p with
  | [::] => 0
  | [:: a] => size (children_of_forest left) + a
  | a :: p =>
    let left := children_of_forest left in
    let right := children_of_forest right in
    size left + size right +
    count_smaller_fix (left ++ take a right) (drop a right) p
  end.

Definition count_smaller_rec l f p := nosimpl count_smaller_fix l f p.

Definition count_smaller t p :=
  if p is [::] then 0 else (count_smaller_rec [::] [:: t] p).+1.

Lemma count_smaller_rec_last l f a :
  count_smaller_rec l f [:: a] = size (children_of_forest l) + a.
Proof. by []. Qed.

Lemma count_smaller_rec_cons_cons a p left right :
  size p != 0 ->
  count_smaller_rec left right (a :: p) =
  size (children_of_forest left) + size (children_of_forest right) +
  count_smaller_rec
    (children_of_forest left ++ take a (children_of_forest right))
    (drop a (children_of_forest right)) p.
Proof. by case: p. Qed.

Lemma count_smaller_grow a p t :
  count_smaller t p = (count_smaller (Node a [:: t]) (0 :: p)).-1.
Proof. by []. Qed.

Theorem breadth_first_ind (P : forest A -> forest A -> seq nat -> Prop):
  (forall l r a, P l r [:: a]) ->
  (forall left right a p,
      let left' := children_of_forest left in
      let right' := children_of_forest right in
      size p != 0 ->
      P (left' ++ take a right') (drop a right') p ->
      P left right (a :: p)) ->
  forall l r p, size p != 0 -> P l r p.
Proof.
move=> H1 Hn l r p.
elim: p l r => // a [|b p] IH l r Hp //.
by apply Hn, IH.
Qed.

Definition LOUDS_position (t : tree A) (p : seq nat) :=
   (count_smaller t p + (count_smaller t (rcons p 0)).-1).+2.
(* ((number of false) + (number of true)).+start position *)

Lemma LOUDS_subtree_rcons B p x :
  LOUDS_subtree B (rcons p x) = LOUDS_child B (LOUDS_subtree B p) x.
Proof.
by rewrite /LOUDS_subtree -cats1 foldl_cat.
Qed.

Variable dA : A.
Notation dummy := (Node dA [::]).

Lemma children_of_forest_height h (l : forest A) :
  all [pred t | height t <= h.+1] l ->
  all [pred t | height t <= h] (children_of_forest l).
Proof.
move=> /allP H; apply/allP => t /flatten_mapP [[a l'] l'l tl'] /=.
move: tl' (H _ l'l) => /=; rewrite ltnS big_map.
rewrite -(in_tupleE l') big_tuple => /tnthP [i ->] /bigmax_leqP.
exact.
Qed.

(* NB(rei): not used? *)
Lemma subseq_children_of_forest a (l : forest A):
  subseq (children_of_forest (take a l)) (children_of_forest l).
Proof.
elim : a l => [l|a IH [|h t] //=]; first by rewrite take0 sub0seq.
by rewrite !children_of_forest_cons cat_subseq.
Qed.

(* wip *)
Lemma size_flatten_node_description (l : forest A) :
  size (flatten [seq node_description i | i <- children_of_forest' l]) =
  size l + size (children_of_forest l).
Proof.
elim: l => //= t f IH; rewrite children_of_forest_cons [in RHS]size_cat.
by rewrite addSn addnCA -IH size_cat size_node_description addSn.
Qed.

(* wip, not used *)
Lemma rank_children_of_forest (l : forest A) a : a <= size l ->
  rank false (a + size (children_of_forest (take a l)))
    (flatten [seq node_description i | i <- children_of_forest' l]) = a.
Proof.
elim: a l => [|a IH] l Hl /=; first by rewrite take0 rank0.
destruct l as [|t l]=> //=.
rewrite children_of_forest_cons.
rewrite size_cat addSn addnCA -addSn.
rewrite rank_addn.
rewrite rank_cat size_node_description ltnn subnn rank0 addn0.
rewrite rank_size ?size_node_description //.
rewrite count_mem_false_node_description add1n; congr S.
by rewrite drop_size_cat ?size_node_description // IH.
Qed.

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

(* not used *)
Lemma rank_true_node_description (l : forest A) a :
  a <= size l -> rank true a (node_description l) = a.
Proof.
move=> Ha; rewrite -{1}(select_true_node_description Ha).
by rewrite selectK //= count_mem_true_node_description.
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

Lemma nth_head_drop (T : eqType) (dT : T) n s :
  nth dT s n = head dT (drop n s).
Proof. by rewrite -{1}(addn0 n) -nth_drop nth0. Qed.

Lemma valid_position_drop r a p :
  valid_position (head dummy r) (a :: p) ->
  valid_position (head dummy (drop a (children_of_forest r))) p.
Proof.
destruct r as [|t r] => //.
rewrite valid_position_cons /= => /andP[Ha].
rewrite -nth_head_drop children_of_forest_cons nth_cat Ha.
by rewrite (set_nth_default t).
Qed.

Lemma ltn_valid_position_size r a p :
  valid_position (head dummy r) (a :: p) ->
  0 < size (children_of_forest r) -> a < size (children_of_forest r).
Proof.
rewrite valid_position_cons => /andP [Ha _] H0.
apply (leq_trans Ha).
rewrite size_children_of_node_forest // -nth0 mem_nth //; by destruct r.
Qed.

Lemma all_height_gt0 h (l : forest A) :
  0 < size l -> all [pred t | height t <= h] l -> 0 < h.
Proof. case: h l => // -[|a l] //= _; by rewrite leqNgt height_gt0. Qed.

Theorem LOUDS_select_false (t : tree A) (p : seq nat) :
  valid_position t p ->
  LOUDS_position t p = select false (count_smaller t p).+1 (LOUDS t).
Proof.
move=> HV.
rewrite /LOUDS /LOUDS_position /=; do 2 congr S.
rewrite (count_smaller_grow dA) (count_smaller_grow dA (rcons p 0)).
rewrite /count_smaller !succnK -rcons_cons.
set t' := Node dA [:: t].
set p' := (0 :: p).
set left := [::].
set right := [:: t'].
rewrite -subn1 (_ : 1 = size (children_of_forest (left ++ right))) //.
have {HV}HV : valid_position (head dummy right) p' by [].
rewrite /lo_traversal.
rewrite (_ : [:: t] = children_of_forest (left ++ right)) //.
set h := height t.
have Hh : all [pred t | height t <= h] (children_of_forest (left ++ right)).
  by apply/allP => x /=; rewrite mem_seq1 => /eqP ->.
have Hr: size (children_of_forest right) > 0 by [].
have Hp: size p' != 0 by [].
move: {t p t'} left right p' Hp h Hh Hr HV.
apply: breadth_first_ind => [l r a|l r a p left right Hp IH] h Hh Hr HV.
- rewrite /count_smaller_rec /= addn0.
  move: Hr Hh.
  rewrite (children_of_forest_cat l).
  set l' := children_of_forest l.
  set r' := children_of_forest r.
  move=> Hr'.
  case: h => [|h _] /=.
    by rewrite all_cat => /andP [_] /(all_height_gt0 Hr').
  rewrite -size_cat addKn /lo_traversal'.
  have -> : l' ++ take a r' = take (size l' + a) (l' ++ r').
    by rewrite take_cat ifF ?ltnNge ?leq_addr // addnC addnK.
  have {Hr' HV}Hr' := ltn_valid_position_size HV Hr'.
  rewrite select_cat ifT; last first.
    rewrite count_mem_false_flatten_node_description size_map size_cat.
    by rewrite leq_add2l ltnW.
  by rewrite select_false_children_of_forest // size_cat leq_add2l ltnW.
- rewrite !rcons_cons !count_smaller_rec_cons_cons ?size_rcons //.
  rewrite !children_of_forest_cat -/left -/right in IH Hr Hh *.
  destruct h as [|h].
    by move: Hh; rewrite all_cat => /andP [_] /(all_height_gt0 Hr).
  rewrite /lo_traversal' /= select_addn.
  rewrite count_cat count_mem_false_flatten_node_description.
  rewrite size_map size_cat leq_addr.
  rewrite select_cat count_mem_false_flatten_node_description.
  rewrite size_map size_cat leqnn.
  rewrite select_false_children_of_forest; last by rewrite size_cat.
  rewrite drop_cat size_flatten_node_description -size_cat take_size ltnn.
  rewrite subnn drop0 addKn -2!addnA; congr addn.
  rewrite -catA -!children_of_forest_cat cat_take_drop in IH.
  rewrite -{}IH.
  (* Conclusion *)
  + rewrite addnA (addnC (size _)) -addnA subnKC //.
    destruct p as [|b p] => //.
    rewrite rcons_cons count_smaller_rec_cons_cons ?size_rcons //.
    rewrite -!size_cat -!children_of_forest_cat -catA cat_take_drop.
    by rewrite children_of_forest_cat leq_addr.
  (* Hh *)
  + rewrite -children_of_forest_cat children_of_forest_height //.
    by rewrite children_of_forest_cat.
  (* Ha *)
  + have:= valid_position_drop HV; rewrite /= -/right.
    destruct p as [|b p] => //= /andP [] /(leq_ltn_trans (leq0n _)).
    have:= size_drop a right; case: (drop a _) => //= t' l' _.
    by rewrite children_of_forest_cons size_cat addn_gt0 => ->.
  (* HV *)
  + by apply valid_position_drop.
Qed.

Lemma size_children_number_of_nodes (t : tree A) :
  size (children_of_node t) <= number_of_nodes t.
Proof.
case: t => [? cl] /=.
rewrite number_of_nodes_Node leqW //.
rewrite sumnE -sum1_size big_map leq_sum // => i _.
by apply number_of_nodes_gt0.
Qed.

Definition valid_position' (t : tree A) p :=
  valid_position t p ||
  if p is x :: p' then (last x p' == 0) && valid_position t (belast x p')
  else false.

Lemma sum_number_of_nodesE (l : forest A) :
  \sum_(t <- l) number_of_nodes t =
  size l + \sum_(t <- l) \sum_(c <- children_of_node t) number_of_nodes c.
Proof.
rewrite -sum1_size -big_split /=; apply eq_bigr => c _.
by rewrite number_of_nodes_Node sumnE big_map add1n.
Qed.

Lemma count_smaller_rec_number_of_nodes left right p :
  size p != 0 -> valid_position' (head dummy right) p ->
  size (left ++ right) +
  (count_smaller_rec left right p + valid_position (head dummy right) p) <=
  \sum_(c <- left ++ right) number_of_nodes c.
Proof.
move: left right p; apply: breadth_first_ind => left right a.
  move=> HV.
  rewrite sum_number_of_nodesE leq_add2l count_smaller_rec_last.
  rewrite big_cat /= size_flatten sumnE big_map big_map -addnA.
  apply leq_add.
    apply leq_sum => i _; by rewrite sum_number_of_nodesE leq_addr.
  rewrite andbT.
  apply (@leq_trans (size (children_of_node (head dummy right)))).
    move/orP: HV => /= [] /andP [Ha _]; first by rewrite Ha addn1.
    rewrite (eqP Ha) add0n; by case H0: (0 < _).
  destruct right as [|t right] => //=.
  by rewrite big_cons sum_number_of_nodesE -addnA leq_addr.
move=> p left' right' Hp; rewrite -catA cat_take_drop => IH HV.
rewrite sum_number_of_nodesE leq_add2l count_smaller_rec_cons_cons //.
rewrite -/left' -/right' -size_cat.
rewrite -(big_map (@children_of_node A) xpredT
                  (fun l => \sum_(c <- l) number_of_nodes c)).
rewrite -big_flatten [X in _ <= X]/= -/(children_of_forest (left++right)).
rewrite children_of_forest_cat.
apply: (leq_trans _ (IH _)).
  rewrite addnA leq_add2l.
  case HV': (valid_position _ (a::p)) => //.
  by rewrite valid_position_drop.
move: HV.
rewrite /valid_position'.
move/orP => [].
  by move/valid_position_drop => /= ->.
destruct p as [|b p] => //.
rewrite last_cons [belast _ _]/= => /andP [-> HV'].
by rewrite (valid_position_drop HV') orbT.
Qed.

Lemma count_smaller_number_of_nodes' t p :
  valid_position' t p ->
  count_smaller t p + valid_position t p <= number_of_nodes t.
Proof.
move=> HV.
rewrite /count_smaller.
destruct p as [|b p] => //.
  apply (@leq_trans true). by case: (valid_position _ _).
  by apply number_of_nodes_gt0.
move: (@count_smaller_rec_number_of_nodes [::] [:: t] (b :: p)).
by rewrite big_seq1 => ->.
Qed.

Corollary count_smaller_number_of_nodes t p :
  valid_position t p ->
  count_smaller t p < number_of_nodes t.
Proof.
move=> HV.
move: (@count_smaller_number_of_nodes' t p).
by rewrite /valid_position' HV addn1 /=; apply.
Qed.

Lemma LOUDS_position_size t p :
  valid_position t p ->
  LOUDS_position t p < size (LOUDS t).
Proof.
move=> HV.
rewrite /LOUDS_position /LOUDS /= 2!ltnS size_level_order_traversal.
rewrite -(@ltn_add2r 1) -addnA -!subn1 subnK ?subnK.
+ rewrite -addnn -addSn.
  apply leq_add; first by apply count_smaller_number_of_nodes.
  apply (leq_trans (leq_addr (valid_position t (rcons p 0)) _)).
  apply count_smaller_number_of_nodes'.
  rewrite /valid_position'.
  destruct p => /=; first by rewrite orbT.
  by rewrite last_rcons belast_rcons eqxx HV orbT.
+ by rewrite -muln2 muln_gt0 /= number_of_nodes_gt0.
+ by destruct p.
Qed.

Lemma count_smaller_LOUDS_false t p :
  valid_position t p -> count_smaller t p < count_mem false (LOUDS t).
Proof.
move=> HV.
rewrite -ltnS.
apply: (@select_strict _ false _ _ (LOUDS t)).
rewrite -LOUDS_select_false // -(addn0 ((count_mem _ _).+1)) select_addn.
by rewrite ltnn ltnS ltnW // LOUDS_position_size.
Qed.

Corollary LOUDS_rank_false (t : tree A) (p : seq nat) :
  valid_position t p ->
  rank false (LOUDS_position t p) (LOUDS t) = (count_smaller t p).+1.
Proof.
by move=> ?; rewrite LOUDS_select_false // selectK // count_smaller_LOUDS_false.
Qed.

Corollary LOUDS_rank_true (t : tree A) (p : seq nat) :
  valid_position t p ->
  rank true (LOUDS_position t p) (LOUDS t) = count_smaller t (rcons p 0).
Proof.
move=> HV.
rewrite brank_negbE; last by apply ltnW, LOUDS_position_size.
rewrite /= LOUDS_rank_false // /LOUDS_position.
rewrite subSS -addnS addnC addnK prednK //; by case: p HV.
Qed.

(* Very useful lemma ! *)
Lemma drop_select_cat b m n (l r : bitseq) :
  select b m l = size l ->
  drop (select b (m + n) (l ++ r)) (l ++ r) = drop (select b n r) r.
Proof.
move=> Hsz.
rewrite select_cat_ge; last first.
  rewrite select_addn.
  by case: ifP; [rewrite Hsz leq_addr | rewrite leqW].
by rewrite drop_cat ltnNge leq_addr /= addKn (select_count Hsz) addKn.
Qed.

Lemma drop_LOUDS_position t p :
  valid_position t p ->
  select false 1 (drop (LOUDS_position t p) (LOUDS t)) = (children t p).+1.
Proof.
move=> HV.
set next_false := select false 1.
rewrite LOUDS_select_false // /LOUDS /count_smaller /=.
rewrite /lo_traversal.
destruct p as [|b p] => //.
  destruct t as [s l].
  rewrite /lo_traversal'.
  rewrite select0 drop0 /= cats0.
  rewrite /next_false select_cat count_mem_false_node_description /=.
  by rewrite select_false_node_description.
set p' := (b :: p) in HV *.
set right := [:: t].
set left := [::].
rewrite {2 3}(_ : right = left ++ right) //.
set h := height t.
have Hh : all [pred t | height t <= h] (left ++ right).
  by apply/allP => x /=; rewrite mem_seq1 => /eqP ->.
rewrite (_ : t = head dummy right) // in HV *.
have Hp : size p' != 0 by [].
rewrite -add1n (_ : 1 = size (left ++ right)) //.
move: {b p t} left right p' Hp h Hh HV.
apply: breadth_first_ind.
- move=> l r b h Hh HV.
  rewrite /=.
  destruct r as [|t r] => //.
  destruct h as [|h].
    move: Hh; by rewrite all_cat /= leqNgt height_gt0 andbF.
  rewrite /lo_traversal' /=.
  (* drop the parent level *)
  rewrite drop_select_cat; last first.
    rewrite select_false_children_of_forest // take_size.
    by rewrite size_flatten_node_description.
  destruct t as [s tl]; move: HV => /= /andP [Hb _].
  rewrite -(cat_take_drop b tl) in Hh *.
  have Hb': 0 < size (drop b tl).
    by rewrite size_drop -(ltn_add2r b) add0n subnK // ltnW.
  destruct (drop b tl) as [|t tl'] => //.
  set t' := Node s _ in Hh *.
  destruct h as [|h].
    move/allP: Hh => /(_ t').
    rewrite mem_cat in_cons eqxx orbT => /(_ erefl) /=.
    rewrite map_cat big_cat /= big_cons /=.
    by rewrite !gtn_max andbC ltnNge height_gt0.
  rewrite /=.
  move: (lo_traversal'' _ _ _) => rest.
  rewrite -map_comp children_of_forest_cat map_cat flatten_cat map_comp.
  (* drop left cousins *)
  rewrite -catA drop_select_cat; last first.
    rewrite size_flatten_node_description.
    by rewrite select_false_children_of_forest // take_size.
  rewrite children_of_forest_cons /=.
  rewrite -catA map_cat flatten_cat /= -catA.
  have {Hb'}Hb': b <= size tl by apply ltnW.
  (* drop elder brothers *)
  rewrite map_comp -(addn0 b) drop_select_cat; last first.
    rewrite size_flatten_node_description addn0.
    rewrite select_false_children_of_forest size_takel //.
    by rewrite (@take_oversize _ _ (take b tl)) // size_takel.
  rewrite select0 drop0.
  (* count the children *)
  rewrite /next_false !select_cat count_cat count_mem_false_node_description /=.
  rewrite select_false_node_description /t' /= addn0.
  by rewrite /children /= nth_cat size_takel // ltnn subnn.
- move => left right b p left' right' Hp IH h Hh HV.
  rewrite [b :: p]lock.
  destruct right as [|t right] => //.
  move: HV; rewrite /= => /andP [Hb HV].
  destruct h as [|h].
    by move: Hh; rewrite all_cat /= leqNgt height_gt0 andbF.
  rewrite /lo_traversal' /=.
  (* drop one level *)
  rewrite drop_select_cat; last first.
    rewrite size_flatten_node_description.
    by rewrite select_false_children_of_forest // take_size.
  rewrite children_of_forest_cat.
  rewrite -lock count_smaller_rec_cons_cons // -/left' -/right'.
  rewrite -(cat_take_drop b right') -size_cat (catA left') cat_take_drop.
  rewrite IH //.
  + by rewrite -nth_head_drop nth_cat Hb (set_nth_default t).
  + rewrite -catA cat_take_drop -children_of_forest_cat.
    by apply children_of_forest_height.
  + by rewrite -nth_head_drop nth_cat Hb (set_nth_default t).
Qed.

Lemma valid_position_leq (t : tree A) p a b :
  valid_position t (rcons p a) -> b <= a -> valid_position t (rcons p b).
Proof.
elim: p t => //= [|c p IH] t /andP [Ha HV] Hb.
  by rewrite (leq_trans _ Ha).
by rewrite Ha IH.
Qed.

Lemma valid_position_children (t : tree A) p a :
  valid_position t (rcons p a) -> a < children t p.
Proof. elim: p t => [|b p IH] t /= /andP [Ha HV] //; by rewrite IH. Qed.

Lemma rank_true_drop_LOUDS_position' t p a :
  valid_position t (rcons p a) ->
  rank true a.+1 (drop (LOUDS_position t p) (LOUDS t)) = a.+1.
Proof.
move=> HV.
move: (valid_position_children HV).
move/valid_position_rcons/drop_LOUDS_position: HV.
elim: (drop _ _) (children t p) a => [|b B IH] c a /=; first by move=> [] <-.
case: ifP => Hif []; first by rewrite select0 => <-.
case: a c => [|a] [|c] // Hs Ha.
  rewrite rank_cons rank0 addn0; by destruct b.
rewrite rank_cons (IH c a) //; by destruct b.
Qed.

Corollary rank_true_drop_LOUDS_position t p a :
  valid_position t (rcons p a) ->
  rank true a (drop (LOUDS_position t p) (LOUDS t)) = a.
Proof.
case: a => [|a] HV; first by rewrite rank0.
rewrite rank_true_drop_LOUDS_position' //.
by apply (valid_position_leq HV).
Qed.

Lemma count_smaller_addn t p a b :
  valid_position t (rcons p (a+b)) ->
  count_smaller t (rcons p (a+b)) = count_smaller t (rcons p a) + b.
Proof.
rewrite /count_smaller.
case: p => // c p HV.
rewrite !rcons_cons -!rcons_cons addSn; congr succn.
rewrite (_ : t = head dummy [:: t]) // in HV.
have Hp: size (c::p) != 0 by [].
set right := [:: t] in HV *.
set left := [::].
move: {c p t} left right (c :: p) Hp HV.
apply: breadth_first_ind => l r c.
+ move=> HV; rewrite /= -[RHS]addnA; congr addn; by rewrite addnA.              + move=> p left right Hp IH HV.
  rewrite !rcons_cons !count_smaller_rec_cons_cons ?size_rcons //.
  rewrite -[RHS]addnA; congr addn.
  apply IH.
  rewrite rcons_cons in HV; by apply valid_position_drop.
Qed.

Lemma LOUDS_rank_true_child t p a :
  valid_position t (rcons p a) ->
  rank true (LOUDS_position t p + a) (LOUDS t) = count_smaller t (rcons p a).
Proof.
move=> HV.
have HV' := valid_position_rcons HV.
rewrite rank_addn.
rewrite LOUDS_rank_true // rank_true_drop_LOUDS_position //.
by rewrite -count_smaller_addn.
Qed.

Theorem LOUDS_positionE (t : tree A) (p : seq nat) :
  let B := LOUDS t in
  valid_position t p ->
  LOUDS_position t p = LOUDS_subtree B p.
Proof.
move=> B.
elim/last_ind: p => [|p a IH] //= HV.
have HV' := valid_position_rcons HV.
rewrite LOUDS_subtree_rcons /LOUDS_child -IH // LOUDS_rank_true_child //.
by apply LOUDS_select_false.
Qed.

Theorem LOUDS_childE (t : tree A) (p : seq nat) x :
  let B := LOUDS t in
  valid_position t (rcons p x) ->
  LOUDS_child B (LOUDS_position t p) x = LOUDS_position t (rcons p x).
Proof.
move=> B HV.
rewrite !LOUDS_positionE // ?(valid_position_rcons HV) //.
by rewrite /LOUDS_subtree -cats1 foldl_cat.
Qed.

End child.

Module LOUDS_position_test.

Definition t' : tree unit := Node tt
  [:: Node tt (Node tt [::] :: Node tt [::] :: nil);
      Node tt [:: Node tt [::]]].

Lemma height_t' : height t' = 3.
Proof. by rewrite /height /= BigOp.bigopE. Qed.

Lemma LOUDS_t' : LOUDS t' = [:: true; false;
  true; true; false; true; true; false; true; false; false; false; false].
Proof. by rewrite /LOUDS /lo_traversal height_t'. Qed.

Eval compute in count_smaller t' (0 :: 1 :: [::]). (* 4 *)
Eval compute in count_smaller t' (0 :: 1 :: 0 :: [::]). (* 6 *)
Eval compute in LOUDS_position t' (0 :: 0 :: [::]). (* 10 *)
Eval compute in LOUDS_position t' (1 :: 0 :: [::]). (* 12 *)

Definition t : tree nat := Node 1
[:: Node 2 [:: Node 5 [::]; Node 6 [::]];
    Node 3 [::];
    Node 4 [:: Node 7 [::]; Node 8 [:: Node 10 [::]]; Node 9 [::]]].

Lemma height_t : height t = 4.
Proof. by rewrite /height /= BigOp.bigopE. Qed.

Lemma LOUDS_t : LOUDS t = [:: true; false;
  true; true; true; false; true; true; false; false; true; true; true; false;
  false; false; false; true; false; false; false].
Proof. by rewrite /LOUDS /lo_traversal height_t. Qed.

Definition p8 := [:: 2; 1].
Definition p4 := [:: 2].

Eval compute in LOUDS_position t [::].
Eval compute in LOUDS_position t [:: 1]. (* 9 *)
Eval compute in count_smaller t p4. (* 3 *)
Eval compute in count_smaller t (rcons p4 0). (* 6 *)
Eval compute in LOUDS_position t p4. (* 10 *)
Eval compute in count_smaller t p8. (* 7 *)
Eval compute in count_smaller t (rcons p8 0). (* 9 *)
Eval compute in LOUDS_position t p8. (* 17 *)

End LOUDS_position_test.

Section children.

Variable A : eqType.

(* see [Navarro, p.214, l.-1] *)
Definition LOUDS_children (B : bitseq) (v : nat) : nat :=
  succ false B v.+1 - v.+1.

Variable dA : A.

(* TODO: prove that LOUDS_children coincides with children (the definition using trees) *)
Theorem LOUDS_childrenE (t : tree A) (p : seq nat) :
  let B := LOUDS t in
  valid_position t p ->
  children t p = LOUDS_children B (LOUDS_position t p).
Proof.
move=> B HV.
rewrite /LOUDS_children /succ.
have Hdrop := drop_LOUDS_position dA HV.
rewrite LOUDS_rank_false // LOUDS_select_false //.
rewrite -(cat_take_drop (select false (count_smaller t p).+1 B) B).
rewrite select_cat ifF; last first.
  rewrite -LOUDS_select_false // -/(rank false (LOUDS_position t p) B).
  by rewrite -LOUDS_rank_false // ltnn.
rewrite size_takel -/B; last first.
  by rewrite -LOUDS_select_false // ltnW // LOUDS_position_size.
rewrite -[(select _ _ _).+1]addn1 subnDA addKn.
rewrite -/(rank false (select false (count_smaller t p).+1 B) B).
rewrite -LOUDS_select_false // LOUDS_rank_false //.
by rewrite -addn1 addKn Hdrop subn1.
Qed.

Definition LOUDS_parent (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v B) B in
  pred false B j.

Theorem LOUDS_parentE (t : tree A) p x :
  valid_position t (rcons p x) ->
  LOUDS_parent (LOUDS t) (LOUDS_position t (rcons p x)) =
  LOUDS_position t p.
Proof.
move=> HV.
have HV' := valid_position_rcons HV.
rewrite LOUDS_positionE // LOUDS_subtree_rcons -LOUDS_positionE //.
rewrite /LOUDS_parent /LOUDS_child selectK; last first.
  by rewrite LOUDS_rank_true_child // count_smaller_LOUDS_false.
rewrite rank_addn.
rewrite rank_true_drop_LOUDS_position //.
rewrite -addSn select_addn ifT; last first.
  rewrite -[in X in _ < X](cat_take_drop (LOUDS_position t p) (LOUDS _)).
  rewrite count_cat -addn1 leq_add2l.
  rewrite -(cat_take_drop x.+1 (drop _ _)) count_cat.
  by rewrite [X in _ < X + _]rank_true_drop_LOUDS_position'.
have HV0 : valid_position t (rcons p 0) by apply (valid_position_leq HV).
rewrite -addn1 -(rank_true_drop_LOUDS_position' dA HV0).
rewrite -rank_addn addn1 -/(pred _ _ _) pred_is_self; first last.
  by rewrite rank_true_drop_LOUDS_position'.
have /rank_same_nseq Htk := rank_true_drop_LOUDS_position' dA HV.
move: (Htk).
rewrite (drop_nth true); last by apply LOUDS_position_size.
rewrite take_cons [nseq  _ _]/= => /eqP.
rewrite eqseq_cons => /andP [/eqP Hnth /eqP Hseq].
rewrite select_all_same //.
(* NB(rei): unconvincing tentative of lemma extraction
Lemma pred_false_LOUDS_position_addn (t : tree A) p x :
  valid_position t (rcons p x) ->
  x < size (LOUDS t) - LOUDS_position t p ->
  pred false (LOUDS t) ((LOUDS_position t p).+1 + x) =
  pred false (LOUDS t) (LOUDS_position t p).
Proof.
move=> tpx Hx.
rewrite /pred addSnnS rank_addn (@brank_negbE (drop _ _)) ?size_drop //.
by rewrite rank_true_drop_LOUDS_position' // subnn addn0.
Qed.

Lemma pred_false_LOUDS_position (t : tree A) p : valid_position t p ->
  pred false (LOUDS t) (LOUDS_position t p) = LOUDS_position t p.
Proof.
move=> tp.
by rewrite LOUDS_select_false // /pred selectK // count_smaller_LOUDS_false.
Qed.

rewrite pred_false_LOUDS_position_addn //; last first.
  rewrite -size_drop -(cat_take_drop x.+1 (drop _ _)) Htk.
  by rewrite size_cat size_nseq leq_addr.
by rewrite pred_false_LOUDS_position.*)
rewrite /pred addSnnS.
rewrite rank_addn.
rewrite (@brank_negbE (drop _ _)); last first.
  rewrite -(cat_take_drop x.+1 (drop _ _)) Htk.
  by rewrite size_cat size_nseq leq_addr.
rewrite rank_true_drop_LOUDS_position' //.
rewrite subnn addn0.
by rewrite LOUDS_select_false // selectK // count_smaller_LOUDS_false.
Qed.

Definition LOUDS_childrank (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v.-1 B) B in
  j - pred false B j.

End children.
