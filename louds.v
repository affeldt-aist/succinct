From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require Import compact_data_structures rank_select pred_succ.

(** * A formalization of LOUDS trees *)

(** OUTLINE:
  0. Section louds_encoding
  1. Section position
       Section lo_traversal
       Definition LOUDS_child/Theorem LOUDS_childE
       Definition LOUDS_parent/Theorem LOUDS_parentE
       Definition LOUDS_children/Theorem LOUDS_childrenE
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section louds_encoding.

Variable A : eqType.
Implicit Types l : forest A.

Definition node_description l := rcons (nseq (size l) true) false.
Definition children_description t := node_description (children_of_node t).

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

Definition LOUDS t := flatten (lo_traversal_st children_description t).

Lemma size_LOUDS t : size (LOUDS t) = (number_of_nodes t).*2.-1.
Proof.
rewrite /LOUDS.
elim/tree_ind_eqType: t => a l IH /=.
rewrite size_cat size_node_description addSn; congr S.
rewrite -doubleE foldr_big_eq.
rewrite (@big_morph nat (seq (seq (seq bool)))
         (fun i => size (flatten (flatten i))) 0 addn nil) //; first last.
  elim => // x xs IHx [] //= y ys.
  by rewrite !flatten_cat !size_cat IHx !addnA (addnAC (size (flatten x))).
rewrite big_seq_cond /=.
rewrite (eq_bigr (fun t => (number_of_nodes t).*2.-1)) /=; last first.
  by move=> i /andP [Hi _]; rewrite IH.
rewrite -big_seq_cond -sum1_size -big_split /=.
rewrite size_flatten /shape -map_comp sumnE big_map -muln2 big_distrl /=.
apply eq_bigr => -[??] _.
by rewrite add1n prednK ?muln2.
Qed.

End louds_encoding.

(*
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
*)

Section position.

Variable A : eqType.
Implicit Types (t : tree A) (l : forest A).

Section lo_traversal.
Variable B : Type.
Variable f : tree A -> B.

Fixpoint lo_traversal_lt (w : forest A) (p : seq nat) : seq B :=
  match p, w with
  | nil, _ | _, nil => nil
  | n :: p', t :: w' =>
    let cl := children_of_node t in
    map f (w ++ take n cl) ++
    lo_traversal_lt (drop n cl ++ children_of_forest (w' ++ take n cl)) p'
  end.

Fixpoint lo_traversal_res (w : forest A) (p : seq nat) : forest A :=
  match p, w with
  | nil, _ => w
  | _, nil => nil
  | n :: p', t :: w' =>
    let cl := children_of_node t in
    lo_traversal_res (drop n cl ++ children_of_forest (w' ++ take n cl)) p'
  end.

Lemma lo_traversal_lt_cat w p1 p2 :
  lo_traversal_lt w (p1 ++ p2) =
  lo_traversal_lt w p1 ++ lo_traversal_lt (lo_traversal_res w p1) p2.
Proof.
elim: p1 w => //= n l IH [|t w].
  by case: p2 {IH}.
by rewrite IH !catA.
Qed.

Lemma lo_traversal_lt_cons w n p :
  lo_traversal_lt w (n :: p) =
  lo_traversal_lt w [:: n] ++ lo_traversal_lt (lo_traversal_res w [:: n]) p.
Proof. exact (lo_traversal_lt_cat w [:: n] p). Qed.

Lemma lo_traversal_lt_cons0 w p :
  lo_traversal_lt w (0 :: p) =
  map f w ++ lo_traversal_lt (children_of_forest w) p.
Proof.
case: w => [|t w] //=.
  by case: p.
rewrite map_cat -catA; congr (_ :: _ ++ _).
by rewrite take0 drop0 cats0.
Qed.

Lemma bigmax_mem (T : eqType) F (x : T) (s : seq T) :
  x \in s -> F x <= \max_(i <- s) F i.
Proof.
elim: s => // y s IH.
rewrite inE big_cons => /orP [/eqP <- | /IH Ht].
  by rewrite leq_maxl.
by apply (leq_trans Ht), leq_maxr.
Qed.

Lemma lo_traversal_lt_max0 l r h p :
  (forall t, t \in l ++ r -> height t <= h) ->
  size p >= h ->
  map f l ++ lo_traversal_lt (r ++ children_of_forest l) p =
  lo_traversal_lt (l ++ r) (nseq h 0).
Proof.
elim: h p l r => [|h IH] p l r Hh Hp.
  have/nilP : l++r = [::].
    case: (l++r) Hh => // t w /(_ t).
    by rewrite mem_head leqNgt height_gt0 => /(_ isT).
  rewrite /nilp size_cat addn_eq0 => /andP[/nilP -> /nilP ->] /=.
  by case: p Hp.
case: p Hp => // n p.
rewrite [size _]/= ltnS [nseq _ _]/= lo_traversal_lt_cons0 map_cat -catA => Hp.
congr cat.
case: r => [|[a cl] r] in Hh *.
  rewrite !cat0s cats0 -(IH (n::p) [::] (children_of_forest l)) ?cats0 //.
    move=> t /= /flattenP [s] /mapP [t'] Ht' -> Ht.
    move: (Hh t'); rewrite cats0 => /(_ Ht').
    by rewrite -(nodeK t') => /height_Node/(_ _ Ht).
  by rewrite ltnW // ltnS.
rewrite /= !map_cat -!catA.
congr (_ :: _ ++ _).
rewrite catA -map_cat (children_of_forest_cat l) children_of_forest_cons /=.
rewrite -[in cl ++ _](cat_take_drop n cl) !children_of_forest_cat -!catA.
rewrite (catA _ (take n cl)) (catA (drop n cl)).
rewrite -children_of_forest_cat {}IH => // t.
rewrite -catA (catA (take n cl)) cat_take_drop.
rewrite -(children_of_forest_cons (Node a cl)) -children_of_forest_cat.
move/flattenP => [s] /mapP [t'] Ht' -> Ht.
by move/Hh: Ht'; rewrite -(nodeK t') => /height_Node/(_ _ Ht).
Qed.

Theorem lo_traversal_lt_max t p :
  size p >= height t ->
  lo_traversal_lt [:: t] p = lo_traversal_lt [:: t] (nseq (height t) 0).
Proof.
refine (@lo_traversal_lt_max0 [::] [:: t] (height t) p _) => t'.
by rewrite inE => /eqP ->.
Qed.

Theorem lo_traversal_lt_ok (t : tree A) p :
  size p >= height t -> lo_traversal_st f t = lo_traversal_lt [:: t] p.
Proof.
rewrite /lo_traversal_st level_traversal_forest => /lo_traversal_lt_max -> {p}.
set w := [:: t]; set h := height t.
have Hh : forall t, t \in w -> height t <= h.
  by move=> t'; rewrite inE => /eqP ->.
elim: {t} h w Hh => [|h IH] w Hh.
  case: w Hh => // t w /(_ t (mem_head _ _)); by rewrite leqNgt height_gt0.
rewrite [nseq _ _]/= lo_traversal_lt_cons0 -IH.
  by case/boolP: (nilp w) => [/nilP | /level_traversal_eq] ->.
by move=> t /flattenP [s] /mapP [[a cl]] /Hh Ht -> /(height_Node Ht).
Qed.
End lo_traversal.

Variable dA : A.
Notation dummy := (Node dA [::]).

Lemma size_lo_traversal w p :
  valid_position (Node dA w) (0 :: p) ->
  size (lo_traversal_res w p) > 0.
Proof.
elim: p w => [|n p IH] [|[a cl] w] //= /andP [Hn HV].
rewrite IH //= size_cat.
rewrite ltn_addr /=; last by rewrite size_drop ltn_subRL addn0.
case Hd: (drop n cl).
  by move/nilP: Hd; rewrite /nilp size_drop /= subn_eq0 leqNgt Hn.
by move: HV; rewrite -(addn0 n) -nth_drop Hd.
Qed.

Definition LOUDS_lt w p :=
  flatten (lo_traversal_lt (@children_description A) w p).

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

Theorem LOUDS_lt_ok t p :
  size p >= height t -> LOUDS t = LOUDS_lt [:: t] p.
Proof. by rewrite /LOUDS /LOUDS_lt => /lo_traversal_lt_ok ->. Qed.

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

Lemma select_false_node_description l :
  select false 1 (node_description l) = (size l).+1.
Proof. elim: l => //= a l IH; by rewrite IH. Qed.

(* not used *)
Lemma select_true_node_description l i : i <= size l ->
  select true i (node_description l) = i.
Proof. elim: l i => //= [|a l IH] [|i] //; by rewrite ltnS => /IH ->. Qed.

Lemma rank_true_node_description l i : i <= size l ->
  rank true i (node_description l) = i.
Proof.
elim: l i => //= [|a l IH] [|i] //; by rewrite ltnS rank_cons => /IH ->.
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
case: a => [|a] in IH Hl *; last by rewrite subn1 /= IH.
by rewrite take0 /= !addn0 select_false_node_description.
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
rewrite map_comp -/(children_of_forest' (w ++ take n cl)).
rewrite /LOUDS_index /= !size_cat size_node_description !size_map.
rewrite size_cat -addnA -(add1n (size w + _)) select_addn.
rewrite count_cat count_mem_false_node_description /=.
rewrite select_cat count_mem_false_node_description /=.
rewrite select_false_node_description.
congr addn.
rewrite drop_size_cat; last by rewrite size_node_description.
rewrite addnA flatten_cat size_cat.
rewrite {}IH; last by rewrite (valid_position_drop _ HV).
rewrite flatten_cat select_addn count_cat.
rewrite count_mem_false_flatten_node_description size_map (size_cat w) leq_addr.
rewrite select_cat count_mem_false_flatten_node_description.
rewrite size_map (size_cat w) leqnn.
rewrite select_false_children_of_forest; last by rewrite size_cat leqnn.
rewrite size_flatten_node_description size_cat -size_cat.
by rewrite take_size drop_size_cat // size_flatten_node_description.
Qed.

Theorem LOUDS_index_rank w p p' n :
  valid_position (head dummy w) (rcons p n) ->
  LOUDS_index w (rcons p n) =
  size w + rank true (LOUDS_position w p + n) (LOUDS_lt w (rcons p n ++ p')).
Proof.
rewrite /LOUDS_position /LOUDS_lt /LOUDS_index.
elim: p w => [|i p IH] [|[a cl] w] HV //=.
  move: HV => /= /andP [Hi _].
  rewrite map_cat !cats0 size_cat add0n /= !size_map -addSn size_take Hi.
  rewrite rank_cat size_node_description ltnS (ltnW Hi).
  by rewrite rank_true_node_description // ltnW.
rewrite map_comp -/(children_of_forest' (w ++ take i cl)).
rewrite !size_cat !size_map size_cat -addnA -addSn.
congr addn.
rewrite -addnA rank_addn rank_cat ltnn rank_size //.
rewrite count_mem_true_node_description subnn rank0 addn0 drop_cat ltnn.
rewrite subnn drop0.
rewrite {}IH; last by rewrite (valid_position_drop _ HV).
rewrite size_cat !addnA -size_cat cat_take_drop -addnA.
congr addn.
rewrite flatten_cat size_cat -addnA [in RHS]rank_addn flatten_cat.
rewrite drop_cat ltnn subnn drop0.
congr addn.
rewrite rank_cat ltnn subnn rank0 addn0 [in RHS]rank_size //.
rewrite count_flatten -map_comp sumnE big_map.
rewrite size_flatten sumnE big_map; apply eq_bigr => t _ /=.
by rewrite count_mem_true_node_description.
Qed.

(* the tth child node v, see [Navarro, p.215] *)
Definition LOUDS_child (B : bitseq) (v t : nat) :=
  select false (rank true (v + t) B).+1 B.

Theorem LOUDS_childE (t : tree A) (p p' : seq nat) x :
  let B := LOUDS_lt [::t] (rcons p x ++ p') in
  valid_position t (rcons p x) ->
  LOUDS_child B (LOUDS_position [:: t] p) x = LOUDS_position [:: t] (rcons p x).
Proof.
rewrite /LOUDS_child => HV.
rewrite -add1n (_ : 1 = size [::t]) // -LOUDS_index_rank //.
by rewrite (@LOUDS_position_select _ _ p') ?cats0.
Qed.

Lemma take_children_position t p p' x :
  let B := LOUDS_lt [:: t] (rcons p x ++ p') in
  valid_position t p ->
  take (children t p).+1 (drop (LOUDS_position [:: t] p) B)
  = node_description (children_of_node (subtree t p)).
Proof.
move=> B HV.
rewrite /B /LOUDS_position -cats1 -catA LOUDS_lt_cat drop_cat ltnn subnn drop0.
set w := [:: t].
rewrite (_ : t = head dummy w) // in HV *.
have Hw: size w > 0 by [].
elim: p w Hw HV {B} => [|n p IH] [|[a cl] w] //= Hw.
  rewrite /LOUDS_lt /children /= take_cat size_node_description ltnS ltnn.
  by rewrite subnn take0 cats0.
move=> /andP [Hn].
set w' := drop n cl ++ _.
rewrite /children /= (set_nth_default dummy _ Hn) nth_head_drop.
have -> : head dummy (drop n cl) = head dummy w'.
  by rewrite -!nth0 /w' nth_cat size_drop ltn_subRL addn0 Hn.
move/IH => -> //.
by rewrite size_cat size_drop ltn_addr // ltn_subRL addn0.
Qed.

Lemma rank_false_LOUDS_position t p p' x :
  valid_position t (rcons p x) ->
  rank false x.+1 (drop (LOUDS_position [:: t] p)
                        (LOUDS_lt [:: t] (rcons p x ++ p'))) = 0.
Proof.
move => HV.
rewrite -(cat_take_drop (children t p).+1 (drop _ _)).
rewrite take_children_position ?(valid_position_rcons HV) //.
rewrite /rank /node_description -cats1 -catA takel_cat.
  by apply /count_memPn /negP => /mem_take /nseqP /andP.
by rewrite size_nseq valid_position_children.
Qed.

Lemma LOUDS_index_leq_count_mem_false t p p' x :
  LOUDS_index [:: t] (rcons p x) <=
  (count_mem false) (LOUDS_lt [:: t] (rcons p x ++ p')).
Proof.
rewrite /LOUDS_index /LOUDS_lt.
elim: {p} (rcons p x) [:: t] => // n p IH [|[a cl] w] //=.
rewrite size_cat size_map.
rewrite count_cat count_mem_false_node_description.
rewrite flatten_cat count_cat map_comp.
rewrite count_mem_false_flatten_node_description size_map add1n ltnS.
by rewrite leq_add2l.
Qed.

(* Cannot move it to rank_select because pred_is_self is in pred_succ *)
Lemma nth_brankK b n B :
  nth (negb b) B n = b -> select b (rank b n B).+1 B = n.+1.
Proof.
move/nth_brank1 => Hrk; move/pred_is_self: (Hrk).
by rewrite /pred -addn1 rank_addn Hrk addn1.
Qed.

Lemma nth_LOUDS_position t p p' x :
  valid_position t (rcons p x) ->
  nth false (LOUDS_lt [:: t] (rcons p x ++ p')) (LOUDS_position [:: t] p + x).
Proof.
move=> HV; move/rank_false_LOUDS_position: (HV) => /(_ p').
rewrite /rank -nth_drop => /count_memPn.
case Hx: (nth _ _ _) => //.
rewrite (take_nth (~~ true)).
  by rewrite mem_rcons in_cons Hx eqxx.
move/take_children_position/(f_equal size): (valid_position_rcons HV).
move/(_ x)/(_ p'); rewrite size_take.
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
rewrite cats0.
elim/last_ind: ((_ :: w) ++ _) => // a' cl' _.
rewrite map_rcons -cats1 flatten_cat size_cat /= cats0.
rewrite size_node_description !addnS => -[] ->.
rewrite drop_cat ltnNge leq_addr /= addKn /node_description.
rewrite drop_rcons; last by rewrite size_nseq.
rewrite -{1}(size_nseq (size (children_of_node cl')) true).
by rewrite drop_size /= rank_cons eqxx rank0.
Qed.

Lemma pred_false_LOUDS_position t p p' x :
  valid_position t (rcons p x) ->
  pred false (LOUDS_lt [:: t] (rcons p x ++ p')) (LOUDS_position [:: t] p) =
  LOUDS_position [:: t] p.
Proof.
move/valid_position_rcons.
rewrite /LOUDS_position -cats1 -catA LOUDS_lt_cat.
move Hsz: (size _) => sz HV.
case: sz => [|sz] in Hsz HV *.
  by rewrite /pred rank0 select0.
rewrite pred_is_self //.
set w := [:: t] in Hsz *.
rewrite (_ : t = head dummy w) // in HV.
elim: p {t} w sz (LOUDS_lt _ [:: x & p']) HV Hsz => // n p IH w sz B HV.
rewrite LOUDS_lt_cons size_cat -catA.
case Hp: (size (LOUDS_lt _ p)).
  rewrite addn0 => Hsz.
  rewrite drop_cat Hsz leqnn rank_cat size_drop Hsz -(add1n sz) addnK ltnn.
  by rewrite subnn rank0 addn0 rank_false_last_LOUDS_position.
rewrite addnS => -[Hsz].
rewrite drop_cat -Hsz leqNgt ltnS leq_addr addKn IH //.
by case: w HV {IH Hp Hsz} => // -[a cl] w /valid_position_drop ->.
Qed.

Definition LOUDS_parent (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v B) B in
  pred false B j.

Theorem LOUDS_parentE (t : tree A) p p' x :
  let B := LOUDS_lt [:: t] (rcons p x ++ p') in
  valid_position t (rcons p x) ->
  LOUDS_parent B (LOUDS_position [:: t] (rcons p x)) =
  LOUDS_position [:: t] p.
Proof.
move=> B HV.
rewrite {}/B /LOUDS_parent (LOUDS_position_select p') //.
rewrite selectK; last by apply LOUDS_index_leq_count_mem_false.
rewrite (LOUDS_index_rank p') // add1n.
rewrite nth_brankK; last by apply nth_LOUDS_position.
rewrite -addnS pred_same_of_rank; last by apply rank_false_LOUDS_position.
by apply pred_false_LOUDS_position.
Qed.

(* see [Navarro, p.214, l.-1] *)
Definition LOUDS_children (B : bitseq) (v : nat) : nat :=
  succ false B v.+1 - v.+1.

Theorem LOUDS_childrenE (t : tree A) (p p' : seq nat) :
  let B := LOUDS_lt [:: t] (rcons p 0 ++ p') in
  valid_position t p ->
  children t p = LOUDS_children B (LOUDS_position [:: t] p).
Proof.
move=> B HV.
rewrite /LOUDS_children succ_drop; last first.
  rewrite /LOUDS_position /B cat_rcons LOUDS_lt_cat.
  rewrite size_cat -[X in X < _]addn0 ltn_add2l.
  move: (@size_lo_traversal [:: t] _ HV).
  case: (lo_traversal_res _ _) => //= [t' w] _.
  by rewrite /LOUDS_lt /= size_cat size_node_description addSn.
rewrite -(cat_take_drop (children t p).+1 (drop _ _)).
rewrite take_children_position // select_cat.
by rewrite count_mem_false_node_description select_false_node_description.
Qed.

Definition LOUDS_childrank (B : bitseq) (v : nat) : nat :=
  let j := select true (rank false v.-1 B) B in
  j - pred false B j.

End position.

Section example.

Definition t : tree nat := Node 1
  [:: Node 2 [:: Node 5 [::]; Node 6 [::]];
      Node 3 [::];
      Node 4 [:: Node 7 [::];
                 Node 8 [:: Node 10 [::]];
                 Node 9 [::]]].

Lemma LOUDS_t : LOUDS (Node 0 [:: t]) =
  [:: true; false; true; true; true; false;
      true; true; false; false; true; true; true; false;
      false; false; false; true; false; false; false].
by [].
Qed.

Definition p8 := [:: 2; 1].
Eval compute in LOUDS_position [:: Node 0 [:: t]] [:: 0 & p8].
End example.
