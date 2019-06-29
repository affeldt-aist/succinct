From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.
Require FunctionalExtensionality Wf_nat Recdef.

(** * Basic generic theories to deal with compact data structures *)

(** OUTLINE
  0. Section seq_ext
  1. definition of the type of indices [1,n]
     Module idx, Section mapping, Section idx_prop, Definition tacc
  2. Section tree
  3. Section valid_position.
  4. Section encode_decode_gentree.
  5. Section forest.
  6. Section level_order_traversal.
  7. Section mzip.
  8. Section lo_traversal_st.
  9. Section forest_eqType.
  10. Section binary_search.
  11. Section bfs.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section seq_ext.

Variable T : Type.
Implicit Type s : seq T.

Lemma take_take : forall s a b, a <= b -> take a (take b s) = take a s.
Proof. by elim => // h t H [*|a[//|b] ab]; rewrite ?take0 // !take_cons H. Qed.

Lemma take_nseq B m n (a : B) : take m (nseq n a) = nseq (minn m n) a.
Proof. by elim: m n => [|m IH] [|n] //=; rewrite minnSS IH. Qed.

Lemma drop_drop : forall s a b, drop a (drop b s) = drop (a + b) s.
Proof. by elim => // ?? H [*|a[|b]]; rewrite ?(drop0,addn0) // addnS /= -H. Qed.

Lemma size_reshape r s : size (reshape r s) = size r.
Proof. by elim: r s => // h t IH s /=; rewrite IH. Qed.

Definition shape_dir n s : seq (seq T) := reshape (nseq (size s %/ n) n) s.

Lemma reshape_nseq_drop' n s b a :
  reshape (nseq b n) (drop (a * n) s) =
    [seq take n (drop (x * n) s) | x <- iota a b].
Proof. elim: b s a => [ //| b IH s a /=]; by rewrite -IH mulSn drop_drop. Qed.

Lemma reshape_nseq_drop n s b :
  reshape (nseq b n) s = [seq take n (drop (x * n) s) | x <- iota 0 b].
Proof. move: (@reshape_nseq_drop' n s b 0); by rewrite drop0. Qed.

Lemma foldr1_mulr (e : T) (M : Monoid.law e) l m :
  M (foldr M e l) m = foldr M m l.
Proof.
elim: l => [|a l IH] /=.
  by rewrite Monoid.mul1m.
by rewrite -Monoid.mulmA IH.
Qed.

Lemma eq_in_foldr (T1 : eqType) T2 (f1 f2 : T1 -> T2 -> T2) (s : seq T1) a :
  {in s, f1 =2 f2} -> foldr f1 a s = foldr f2 a s.
Proof.
elim: s => //= t s IH Hs.
rewrite IH ?Hs ?mem_head // => x Hx y.
by rewrite Hs // inE Hx orbT.
Qed.

End seq_ext.

Module idx.

Record t (n : nat) : Type := mkt {
  i :> 'I_n.+1 ;
  i0 : i != ord0
}.

End idx.

Notation "[1, n ]" := (@idx.t n)
  (at level 8, n at level 2, format "[1, n ]").

Lemma idx_ltn0 (n : nat) (y : [1,n]) : 0 < idx.i y.
Proof. by rewrite lt0n; exact: idx.i0. Qed.

Hint Resolve idx_ltn0.

Lemma idx_leq (n : nat) (y : [1,n]) : idx.i y <= n.
Proof. case: y => //= y _; by rewrite -ltnS. Qed.

Coercion idx_coercion (n : nat) := @idx.i n.
Canonical idx_subType (n : nat) := [subType for @idx.i n].
Definition idx_eqMixin (n : nat) := Eval hnf in [eqMixin of [1,n] by <:].
Canonical idx_eqType (n : nat) := Eval hnf in EqType [1,n] (idx_eqMixin n) .
Definition idx_choiceMixin (n : nat) := [choiceMixin of [1,n] by <:].
Canonical idx_choiceType (n : nat) := Eval hnf in ChoiceType [1,n] (idx_choiceMixin n).
Definition idx_countMixin (n : nat) := [countMixin of [1,n] by <:].
Canonical idx_countType (n : nat) := Eval hnf in CountType [1,n] (idx_countMixin n).
Canonical idx_subCountType (n : nat) := [subCountType of [1,n]].
Definition idx_finMixin (n : nat) := Eval hnf in [finMixin of [1,n] by <:].
Canonical idx_finType (n : nat) := Eval hnf in FinType [1,n] (idx_finMixin n).
Canonical idx_subFinType (n : nat) := Eval hnf in [subFinType of [1,n]].

Section mapping.

Definition ord_of' (n : nat) (i : @idx.t n) : 'I_n.
refine (@Ordinal _ i.-1 _).
rewrite prednK //.
exact: (leq_trans (ltn_ord i) (ltnSn _)).
Defined.

Definition ord_of (n : nat) : {ffun (@idx.t n) -> 'I_n} := [ffun x => ord_of' x].

Definition of_ord' (n : nat) (i : 'I_n) : @idx.t n := @idx.mkt _ (lift ord0 i) isT.

Definition of_ord (n : nat) : {ffun 'I_n -> (@idx.t n)} := [ffun x => of_ord' x].

End mapping.

Section idx_prop.

Lemma ord_of_inj (n : nat) : injective (@ord_of n).
Proof.
move=> [i i0] [j j0] /(congr1 val) /= ij; apply/val_inj => /=; move: ij.
move/(congr1 S).
rewrite !ffunE /=; by rewrite !prednK // ?lt0n // => /ord_inj.
Qed.

Lemma ord_ofK (n : nat) : cancel (@ord_of n) (@of_ord n).
Proof.
move=> x.
apply/val_inj/val_inj => /=.
by rewrite /of_ord /ord_of !ffunE /of_ord' lift0 /= prednK // lt0n @idx.i0.
Qed.

Lemma of_ordK (n : nat) : cancel (@of_ord n) (@ord_of n).
Proof. move=> x; apply/val_inj => /=; by rewrite !ffunE. Qed.

Lemma of_ord_inj (n : nat) : injective (@of_ord n).
Proof. exact: (can_inj (@of_ordK n)). Qed.

Lemma card_idx (n : nat) : #| [finType of [1,n]] | = n.
Proof.
rewrite -[RHS](card_ord n) -!cardsT -[RHS](card_imset _ (@of_ord_inj n)).
apply: eq_card => i; rewrite !inE.
apply/esym/imsetP.
case: i => i i0.
have @i1 : i.-1 < n by rewrite prednK // ?lt0n // -ltnS.
exists (Ordinal i1) => //.
apply/val_inj/val_inj => /=.
by rewrite /of_ord ffunE /of_ord' lift0 /= prednK // lt0n.
Qed.

Lemma enum_10 : enum [finType of [1,0]] = [::].
Proof. apply/eqP; by rewrite -size_eq0 -cardE card_idx. Qed.

Lemma val_enum_idx n : map val (enum [finType of [1,n]]) = behead (enum 'I_n.+1).
Proof.
apply (inj_map val_inj).
rewrite -drop1 map_drop.
move: (val_enum_ord n.+1) => /(congr1 behead); rewrite -drop1 => ->.
apply (@eq_from_nth _ O).
  by rewrite !size_map -drop1 size_drop size_iota subn1 /= -enumT -cardE card_idx.
move=> i.
rewrite !size_map -enumT -cardE card_idx => ni.
rewrite -drop1 nth_drop add1n /=; congr nth.
rewrite enumT /= unlock /= pmap_filter; last exact: insubK.
rewrite unlock /=.
set lhs := LHS.
have : O :: lhs = iota O n.+1.
  rewrite {}/lhs {1}/ord_enum -{1}[in iota _ _](add1n n) iota_add add0n cat1s; congr cons.
  rewrite /= /oapp insubT /= insubF //=.
  set x := pmap _ _.
  transitivity (filter predT (map val x)).
    rewrite filter_map; congr (map val _).
    apply: eq_in_filter => /= j.
    rewrite mem_pmap => /mapP[/= m].
    rewrite mem_iota add1n ltnS lt0n => /andP[m0 mn].
    rewrite insubT /= => -[] -> /=; by rewrite insubT.
  rewrite pmap_filter; last exact: insubK.
  rewrite filter_predT.
  transitivity (filter predT (iota 1 n)).
    apply eq_in_filter => j.
    rewrite mem_iota lt0n add1n ltnS => /andP[j0 jn]; by rewrite insubT.
  by rewrite filter_predT.
rewrite -add1n iota_add -val_ord_enum /= -cat1s => /eqP.
rewrite eqseq_cat; last by rewrite size_map /= /ord_enum size_pmap /= addn0 insubT.
by case/andP => _ /eqP.
Qed.

Lemma nth_enum_idx n :
  map (@idx.i _) (enum [finType of [1,n]]) = map (lift ord0) (enum [finType of 'I_n]).
Proof. rewrite val_enum_idx; by rewrite enum_ordS. Qed.

Lemma of_ord_enum n :
  [seq (@of_ord n) i | i <- Finite.enum (ordinal_finType n)] =
  Finite.enum (idx_finType n).
Proof.
destruct n as [|n].
  rewrite -!enumT enum_10.
  apply/eqP; by rewrite -size_eq0 size_map -cardE card_ord.
have x0 : @idx.t n.+1.
  exists (lift ord0 ord0).
  apply/negP => /eqP/(congr1 val) /= /esym.
  apply/eqP; by rewrite neq_bump.
apply (@eq_from_nth _ x0) => /=.
  by rewrite size_map // -enumT -cardE card_ord -enumT -cardE card_idx.
move=> i.
rewrite size_map => ni.
rewrite (nth_map ord0) //= /of_ord ffunE -!enumT.
apply val_inj => /=; apply/val_inj => /=.
rewrite nth_enum_ord; last first.
  move: ni; by rewrite -enumT -cardE card_ord.
move: (nth_enum_idx n.+1).
rewrite -enumT -cardE card_ord in ni.
move/(congr1 (fun x : seq 'I__ => nth ord0 x i)).
rewrite (nth_map ord0) -?cardE ?card_ord //= (nth_map x0) -?cardE ?card_idx //= => ->.
by rewrite /= nth_enum_ord .
Qed.

End idx_prop.

Definition tacc (T : eqType) (n : nat) (B : n.-tuple T) (i : [1,n]) : T :=
  tnth B (@ord_of n i).

Lemma taccE (T : eqType) b n (s : n.-tuple T) j : tacc s j = nth b s j.-1.
Proof. by rewrite /tacc (tnth_nth b) /ord_of ffunE. Qed.

(* trees with arbitrary finite branching *)
Section tree.

Variable A : Type.

Inductive tree := Node : A -> seq tree -> tree.
(* a leaf is a node with an empty list *)

(* induction principle assuming only Type *)
Lemma tree_ind_type (P : tree -> Prop) :
  (forall a l, foldr (fun t => and (P t)) True l -> P (Node a l)) ->
  forall t, P t.
Proof.
move=> indu; fix H 1.
elim => a l; apply indu.
elim: l => [|b l IH]; first by [].
split; [exact: H | exact IH].
Qed.

Definition children_of_node (t : tree) :=
  let: Node _ l := t in l.

Definition label_of_node (t : tree) :=
  let: Node l _ := t in l.

Lemma nodeK (t : tree) : Node (label_of_node t) (children_of_node t) = t.
Proof. by case: t. Qed.

Definition root (T : tree) : A := let: Node w _ := T in w.

(* enumerate nodes: depth-first, pre-order *)
Fixpoint nodes (t : tree) : seq A :=
  let: Node a l := t in a :: flatten (map nodes l).

Definition number_of_nodes (t : tree) := size (nodes t).

Lemma number_of_nodes_gt0 (t : tree) : 0 < number_of_nodes t.
Proof. by case: t. Qed.

Lemma number_of_nodes_Node (t : tree) :
  number_of_nodes t = (sumn (map number_of_nodes (children_of_node t))).+1.
Proof.
case: t => ? ?; by rewrite /number_of_nodes /= size_flatten /shape -map_comp.
Qed.

Definition forest := seq tree.

(* enumerate children: depth-first, pre-order *)
Fixpoint seq_of_tree (B : Type) (f : forest -> seq B) (t : tree) : seq B :=
  let: Node _ l := t in f l ++ flatten (map (seq_of_tree f) l).

Fixpoint height (t : tree) : nat :=
  let: Node _ l := t in (\max_(i <- map height l) i).+1.

Lemma height_gt0 (t : tree) : 0 < height t.
Proof. by case: t. Qed.

Fixpoint subtree (t : tree) (p : seq nat) : tree :=
  match p with
  | nil => t
  | n :: p' =>
    subtree (nth t (children_of_node t) n) p'
  end.

Definition children (t : tree) (p : seq nat) :=
  size (children_of_node (subtree t p)).

Definition child (p : seq nat) (n : nat) := rcons p n.

End tree.
Arguments children_of_node {A}.

Section valid_position.

Variable A : Type.
Implicit Types t : tree A.

Fixpoint valid_position t p :=
  if p isn't n :: p' then true else
  let l := children_of_node t in
  (n < size l) && valid_position (nth t l n) p'.

Lemma valid_position_cons t a p :
  valid_position t (a :: p) = let l := children_of_node t in
    (a < size l) && valid_position (nth t l a) p.
Proof. by []. Qed.

Lemma valid_position_cat t p1 p2 :
  valid_position t (p1 ++ p2) -> valid_position t p1.
Proof. elim: p1 t => //= p ps IH t /andP[H1 H2]; by rewrite H1 /= IH. Qed.

Lemma valid_position_rcons t p x :
  valid_position t (rcons p x) -> valid_position t p.
Proof. by rewrite -cats1 => /valid_position_cat. Qed.

Lemma valid_position_take t p k :
  valid_position t p -> valid_position t (take k p).
Proof. by rewrite -{1}(cat_take_drop k p) => /valid_position_cat. Qed.

Lemma valid_position_height t p : valid_position t p -> size p <= height t.
Proof.
elim: p t => [//|x p IH [a l]].
rewrite valid_position_cons /= ltnS => /andP[Hx HV].
rewrite big_map big_tnth (leq_trans (IH _ HV)) //.
by rewrite -(tnth_nth (Node a l) (in_tuple l) (Ordinal Hx)) leq_bigmax.
Qed.

Lemma valid_position_weaken a1 a2 l1 l2 p :
  valid_position (Node a1 l1) p -> valid_position (Node a2 (l1 ++ l2)) p.
Proof.
case: p => //= a p; rewrite size_cat => /andP[al1]; rewrite ltn_addr //=.
by rewrite nth_cat al1 -(in_tupleE l1) (_ : a = Ordinal al1) // -!tnth_nth.
Qed.

Lemma valid_position_children (t : tree A) p x :
  valid_position t (rcons p x) -> x < children t p.
Proof.
rewrite /children.
by elim: p t => [|n p IH] [a cl] //= /andP [Hn] // /IH.
Qed.

End valid_position.

Section encode_decode_gentree.

Variable A : Type.

Fixpoint encode_tree (t : tree A) : GenTree.tree A :=
  match t with
  | Node a [::] => GenTree.Leaf a
  | Node a l => GenTree.Node O(*dummy*) (GenTree.Leaf a :: map encode_tree l)
  end.

Fixpoint decode_tree (t : GenTree.tree A) : option (tree A) :=
  match t with
  | GenTree.Leaf a => Some (Node a [::])
  | GenTree.Node _ (GenTree.Leaf h :: l) => Some (Node h (pmap decode_tree l))
  | GenTree.Node _ _ => None
  end.

Lemma pcancel_tree : pcancel encode_tree decode_tree.
Proof.
elim/tree_ind_type => a [//|b s /= [-> H2 /=]]; congr (Some (Node _ (_ :: _))).
elim: s H2 => // c s IH /= [-> K2 /=]; by rewrite IH.
Qed.

End encode_decode_gentree.

Definition tree_eqMixin (A : eqType) := PcanEqMixin (@pcancel_tree A).
Canonical tree_eqType (A : eqType) := Eval hnf in EqType _ (@tree_eqMixin A).

Definition tree_choiceMixin (A : choiceType) := PcanChoiceMixin (@pcancel_tree A).
Canonical tree_choiceType (A : choiceType) :=
  Eval hnf in ChoiceType _ (@tree_choiceMixin A).

Definition tree_countMixin (A : countType) := PcanCountMixin (@pcancel_tree A).
Canonical tree_countType (A : countType) :=
  Eval hnf in CountType _ (@tree_countMixin A).

Lemma height_Node (A : eqType) (v : A) l n :
  height (Node v l) <= n.+1 -> forall t, t \in l -> height t <= n.
Proof.
rewrite /= ltnS => Hn t tl; rewrite (leq_trans _ Hn) // {Hn} big_map.
elim: l tl => // a b IH; rewrite inE => /orP[/eqP ->|/IH].
  by rewrite big_cons leq_maxl.
rewrite big_cons leq_max => ->; by rewrite orbT.
Qed.

(* induction principle using eqType (and therefore \in) *)
Lemma tree_ind_eqType (A : eqType) (P : tree A -> Prop) :
  (forall a l, (forall x, x \in l -> P x) -> P (Node a l)) ->
  forall t, P t.
Proof.
move=> H; apply tree_ind_type => a s IH; apply H.
elim: s IH => // b s IH /= [Pb K] t.
by rewrite in_cons => /orP[/eqP -> //|]; apply IH.
Qed.

Section forest.

Variable A : Type.
Implicit Types s : forest A.

Definition labels_of_forest s : seq A := map (fun '(Node v' _) => v') s.

Definition children_of_forest' s : seq (forest A)  := map children_of_node s.

Definition children_of_forest s : forest A := flatten (children_of_forest' s).

Lemma children_of_forest_nil : children_of_forest [::] = [::].
Proof. by []. Qed.

Lemma children_of_forest'_cat s1 s2 : flatten (children_of_forest' (s1 ++ s2)) =
  flatten (children_of_forest' s1) ++ flatten (children_of_forest' s2).
Proof. by rewrite /children_of_forest' map_cat flatten_cat. Qed.

Lemma children_of_forest_cat s1 s2 :
 children_of_forest (s1 ++ s2) = children_of_forest s1 ++ children_of_forest s2.
Proof.
by rewrite /children_of_forest /children_of_forest' map_cat flatten_cat.
Qed.

Lemma children_of_forest_cons a s :
  children_of_forest (a :: s) = children_of_node a ++ children_of_forest s.
Proof. by []. Qed.

End forest.

Section forest_eqType.
Variable A : eqType.
Implicit Types s : forest A.

Lemma children_of_forest_height s n :
  {in s, forall t, height t <= n.+1 } ->
  {in children_of_forest s, forall t, height t <= n}.
Proof.
move=> H t /= /flattenP [s'] /mapP [t'] t's -> tt'.
move: (H t') => /(_ t's).
by rewrite -(nodeK t') => /height_Node/(_ _ tt').
Qed.

Lemma size_children_of_node_forest (t : tree A) l : t \in l ->
  size (children_of_node t) <= size (children_of_forest l).
Proof.
elim: l t => // h l IH t.
rewrite children_of_forest_cons size_cat in_cons => /orP[/eqP ->|/IH].
  by rewrite leq_addr.
by move/leq_trans => -> //; rewrite leq_addl.
Qed.

End forest_eqType.

Section level_order_traversal.

Variables (A B : Type) (f : tree A -> B).

(* n to be instantiated with max of map height l *)
Fixpoint lo_traversal' n (s : forest A) :=
  if n is n'.+1 then
    map f s ++ lo_traversal' n' (children_of_forest s)
  else
    [::].

Definition lo_traversal t := lo_traversal' (height t) [:: t].

End level_order_traversal.

Section mzip.
Import Monoid.Theory.
Variable (A : Type) (e : A) (M : Monoid.law e).

Fixpoint mzip (l r : seq A) {struct l} :=
  match l, r with
  | (l1::ls), (r1::rs) => (M l1 r1) :: mzip ls rs
  | nil, s | s, nil    => s
  end.

Lemma mzipA : associative mzip.
Proof.
elim => [|lh lt IH] [|rh rt] [|sh st] //=.
by rewrite IH mulmA.
Qed.

Lemma mzip1s s : mzip [::] s = s.
Proof. by []. Qed.

Lemma mzips1 s : mzip s [::] = s.
Proof. by case: s. Qed.

Canonical mzip_monoid := Monoid.Law mzipA mzip1s mzips1.

Lemma flatten_mzipC h s1 s2 :
  foldr M e (mzip (h :: s1) s2) = M h (foldr M e (mzip s2 s1)).
Proof.
elim: s2 h s1 => // h2 s2 IH h1 s1 /=.
rewrite -mulmA; congr (M h1).
case: s1 => //= {h1}h1 s1.
rewrite -mulmA -{}IH; by case: s2.
Qed.

Lemma foldr_bigE C (g : C -> A) cl :
  foldr (M \o g) e cl = \big[M/e]_(i <- cl) g i.
Proof. by rewrite BigOp.bigopE. Qed.
End mzip.

Section lo_traversal_st.
Variables (A : eqType) (B : Type) (f : tree A -> B).
Implicit Types s : forest A.

Definition mzip_cat : Monoid.law [::] := mzip_monoid (cat_monoid B).

Fixpoint level_traversal t :=
  [:: f t] :: foldr (mzip_cat \o level_traversal) nil (children_of_node t).

Definition lo_traversal_st t := flatten (level_traversal t).

Definition forest_traversal := foldr (mzip_cat \o level_traversal) nil.

Lemma level_traversal_forest t :
  level_traversal t = forest_traversal [:: t].
Proof. by case: t. Qed.

Lemma level_traversalE t :
  level_traversal t =
  [:: f t] :: \big[mzip_cat/nil]_(i <- children_of_node t) level_traversal i.
Proof. rewrite -foldr_bigE; by case: t. Qed.

Lemma forest_traversalE' st s :
  ~~ nilp s ->
  foldr (mzip_cat \o level_traversal) st s =
  (map f s ++ head nil st) ::
  foldr (mzip_cat \o level_traversal) (behead st) (children_of_forest s).
Proof.
elim: s => //= -[a cl] [|t s'] IH // _.
  rewrite /children_of_forest /=.
  case: {IH} st => [|h st]; rewrite !cats0 //=.
  by rewrite -foldr_map foldr1_mulr foldr_map.
set s := t :: s' in IH *.
move/(_ isT): (IH) => ->.
rewrite children_of_forest_cons /= foldr_cat /=.
by rewrite -!(foldr_map level_traversal mzip_cat) foldr1_mulr.
Qed.

Lemma forest_traversalE s :
  ~~ nilp s ->
  forest_traversal s = map f s :: forest_traversal (children_of_forest s).
Proof.
by move/(forest_traversalE' nil); rewrite /forest_traversal /= cats0 => ->.
Qed.

Theorem lo_traversal_stE t :
  lo_traversal_st t = lo_traversal f t.
Proof.
rewrite /lo_traversal_st level_traversal_forest /lo_traversal.
set s := [:: t]; set h := height t.
have Hh : forall t : tree A, t \in s -> height t <= h.
  by move=> t'; rewrite inE => /eqP ->.
elim: {t} h s Hh => //= [|h IH] s Hh.
  by case: s Hh => // t w /(_ t (mem_head _ _)); rewrite leqNgt height_gt0.
rewrite -IH.
  by case /boolP: (nilp s) => [/nilP | /forest_traversalE] ->.
by move=> t /flattenP [s'] /mapP [[a cl]] /Hh Ht -> /(height_Node Ht).
Qed.

Fixpoint level_traversal_cat (t : tree A) ss {struct t} :=
  (f t :: head nil ss) ::
  foldr level_traversal_cat (behead ss) (children_of_node t).

Definition lo_traversal_cat t := flatten (level_traversal_cat t [::]).

Lemma level_traversal_catE t ss :
  mzip_cat (level_traversal t) ss = level_traversal_cat t ss.
Proof.
elim/tree_ind_eqType: t ss => [a cl] IH ss.
case: ss => [|s ss] /=; congr cons.
  by apply /eq_in_foldr.
rewrite -foldr_map foldr1_mulr foldr_map; by apply /eq_in_foldr.
Qed.

Theorem lo_traversal_catE t : lo_traversal_cat t = lo_traversal_st t.
Proof. by rewrite /lo_traversal_cat -level_traversal_catE Monoid.mulm1. Qed.

End lo_traversal_st.

Goal lo_traversal_st (@label_of_node _)
     (Node 1 [:: Node 2 [:: Node 4 [::]]; Node 3 [::]]) = [:: 1; 2; 3; 4].
by [].
Abort.

Goal lo_traversal_cat (@label_of_node _)
     (Node 1 [:: Node 2 [:: Node 4 [::]]; Node 3 [::]]) = [:: 1; 2; 3; 4].
by [].
Abort.

Section forest_eqType.

Variable A : eqType.
Implicit Types l : forest A.

Lemma all_height_Node l n :
  all (fun x : tree A => height x <= n.+1) l ->
  all (fun x : tree A => height x <= n) (children_of_forest l).
Proof.
elim: l => [|t l IH /= /andP [] Ht Hl]; first by [].
rewrite all_cat.
apply/andP.
split; last by apply IH.
case: t Ht => v' l' /height_Node Hh.
by apply/allP.
Qed.

(*
Lemma level_order_forest_traversal'_nil (B : Type)
  (f : forest A -> seq B) (n : nat) (Hf0 : f [::] = [::]) :
  lo_traversal'' f n [::] = [::].
Proof. by elim: n => [|n /=]; last rewrite Hf0. Qed.

Lemma level_order_forest_traversal'_cat (B : Type)
  (f : forest A -> seq B) (n : nat) l1 l2
  (Hf0 : f [::] = [::])
  (Hf2 : forall x y, f (x ++ y) = f x ++ f y) :
  all (fun x => n >= height x) (l1 ++ l2) ->
  lo_traversal'' f n (l1 ++ l2) =
  f l1 ++ lo_traversal'' f n (l2 ++ children_of_forest l1).
Proof.
elim: n l1 l2 => [l1 l2|n IH l1 l2 H] /=.
  rewrite all_cat.
  case: l1 => [|t l1 /=]; by [rewrite Hf0 | rewrite leqNgt height_gt0].
rewrite children_of_forest_cat {}IH; last first.
  move: H; rewrite all_cat => /andP [? ?]; by rewrite all_cat !all_height_Node.
by rewrite !Hf2 -!catA children_of_forest_cat.
Qed.

Lemma level_order_forest_traversal'_cons (B : Type)
  (f : forest A -> seq B)
  (n : nat) v' l' (t : tree A) l
  (Hf0 : f [::] = [::])
  (Hf2 : forall x y, f (x ++ y) = f x ++ f y) :
  t = Node v' l' ->
  all (fun x => n >= height x) (t :: l) ->
  lo_traversal'' f n (t :: l) =
  f [:: t] ++ lo_traversal'' f n (l ++ l').
Proof.
move=> -> H.
rewrite -cat1s level_order_forest_traversal'_cat //.
by rewrite children_of_forest_cons cats0.
Qed.
*)

End forest_eqType.

Section binary_search.

Variable i : nat.
Variable g : nat -> nat.
Variable def : nat.

Program Definition binarysearch' (ab : nat * nat)
  (f : forall ab', (ab'.2 - ab'.1 < ab.2 - ab.1)%coq_nat -> nat) : nat :=
    let a := ab.1 in let b := ab.2 in
    match Bool.bool_dec (b <= a) true with
    | left _ => if g a == i then a else def
    | right _ =>
      let p := (a + b)./2 in
      let x := g p in
      match Bool.bool_dec (i <= x) true with
      | left _ => f (a, p) _
      | right _ => (* x > i *) f (p.+1, b) _
      end
    end.
Next Obligation.
clear Heq_anonymous Heq_anonymous0 f.
move/negP: wildcard'0; rewrite /= -ltnNge => ab0.
apply/ltP.
by rewrite ltn_sub2r // -divn2 ltn_divLR // muln2 -addnn ltn_add2r.
Qed.
Next Obligation.
clear Heq_anonymous0 Heq_anonymous f.
move/negP : wildcard'0; rewrite /= -ltnNge => ab0.
by apply/ltP; rewrite ltn_sub2l // ltnS -divn2 leq_divRL // muln2 -addnn leq_add2l ltnW.
Qed.

Definition myltn (x y : nat * nat) := (x.2 - x.1 < y.2 - y.1)%coq_nat.

Lemma well_founded_myltn : well_founded myltn.
Proof.
apply (Wf_nat.well_founded_lt_compat _ (fun x : nat * nat => x.2 - x.1)) => x y.
rewrite /myltn => /ltP H; by apply/ltP.
Qed.

Definition binarysearch := Fix well_founded_myltn (fun _ => nat) binarysearch'.

Lemma binarysearch_unfold (x : nat * nat) :
  binarysearch x = @binarysearch' x (fun y _ => binarysearch y).
Proof.
rewrite /binarysearch Fix_eq // => x0 f f' H; congr binarysearch'.
apply FunctionalExtensionality.functional_extensionality_dep => y.
by apply FunctionalExtensionality.functional_extensionality.
Qed.

Hypothesis g_incr : forall x y, x <= y -> g x <= g y.

Lemma intervalsearch_spec (x : nat * nat) : exists k : nat,
  ((x.1 <= k <= x.2) && (g k == i)) || (k == def).
Proof.
case/boolP : [exists k : 'I_(g x.2), (x.1 <= k <= x.2) && (g k == i)] => [|].
  case/existsP=> k Hk; exists (val k).
  by rewrite Hk.
rewrite negb_exists => /forallP /= => H.
exists def.
by apply/orP; right.
Qed.

Definition Intervalsearch x := ex_minn (intervalsearch_spec x).

Lemma g_incr_inv a a' : g a >= i -> g a' == i -> a' >= a -> g a == i.
Proof.
move=> e Ha' Haa'.
move: (g_incr Haa').
rewrite (eqP Ha') => e'.
move/andP: (conj e e').
by rewrite -eqn_leq => /eqP ->.
Qed.

Lemma Intervalsearch_eq x y :
  y.1 <= x.1 -> x.1 <= x.2 -> x.2 <= y.2 -> def > y.2 ->
  (forall a, y.1 <= a < x.1 -> g a < i) ->
  (forall a, x.2 <= a <= y.2 -> g a >= i) ->
  Intervalsearch x = Intervalsearch y.
Proof.
move=> H1 Hx H2 Hdef Hl Hr.
have Hl': forall m, m >= y.1 -> g m == i -> m >= x.1.
  move=> m Hm Hgm.
  case Hxm: (_ <= _) => //.
  move/negP/negP in Hxm.
  have /ltn_eqF: g m < i.
    by rewrite Hl // Hm ltnNge Hxm.
  by rewrite Hgm.
rewrite /Intervalsearch.
case: ex_minnP => m /= /orP [|] Hm Hall;
  case: ex_minnP => m' /= /orP [|] Hm' Hall'.
- have Hm'm: m' <= m.
    apply (Hall' m).
    move/andP: Hm => [] /andP [] Hxm Hmx ->.
    by rewrite (leq_trans H1 Hxm) (leq_trans Hmx H2).
  have Hmm': m <= m'.
    apply (Hall m').
    move/andP: Hm' => [] /andP [] Hym Hmy Hm'.
    move/andP/proj1/andP/proj2: Hm => /(leq_trans Hm'm) ->.
    by rewrite Hm' Hl'.
  apply/eqP.
  by rewrite eqn_leq Hm'm Hmm'.
- have mdef: def <= m.
    rewrite -(eqP Hm'); apply Hall'.
    move/andP: Hm => [] /andP [] Hxm Hmx ->.
    by rewrite (leq_trans H1 Hxm) (leq_trans Hmx H2).
  move/andP/proj1/andP/proj2: Hm => Hmx.
  have: def <= y.2.
    by apply (leq_trans mdef), (leq_trans Hmx).
  by rewrite leqNgt Hdef.
- move/andP: Hm' => [] /andP [Hym' Hm'y] Hm'i.
  have mdef: def <= m'.
    rewrite -(eqP Hm); apply Hall.
    rewrite Hm'i Hl' //.
    case Hm': (m' <= _) => //.
    move/negP/negP in Hm'.
    rewrite -ltnNge in Hm'.
    have Hx2: g x.2 == i.
      rewrite (g_incr_inv _ Hm'i) //.
        by rewrite Hr // leqnn.
      by apply ltnW.
    have Hm'': m' <= x.2.
      by rewrite Hall' // Hx2 H2 (leq_trans H1 Hx).
    by rewrite ltnNge Hm'' in Hm'.
  apply/eqP.
  by rewrite (eqP Hm) eqn_leq mdef Hall' // eqxx orbT.
- by rewrite (eqP Hm) (eqP Hm').
Qed.

Lemma Intervalsearch_out x : ~~ (i <= g x.2) -> Intervalsearch x = def.
Proof.
rewrite /Intervalsearch => Hi.
case: ex_minnP => m /= /orP [|/eqP //] Hm Hall.
move/andP: Hm => [] /andP [_ /g_incr Hma'] Hgm.
by rewrite -(eqP Hgm) Hma' in Hi.
Qed.

Lemma Intervalsearch_one a :
  a < def -> Intervalsearch (a,a) = if g a == i then a else def.
Proof.
rewrite /Intervalsearch => Hdef.
case: ex_minnP => m /= Hm Hall.
case: ifPn.
  case/orP: Hm => [/andP [] | /eqP Hm gx1i].
    by rewrite -eqn_leq => /eqP.
  move: (Hall a) Hdef.
  by rewrite ltnNge Hm gx1i !leqnn /= => ->.
case/orP: Hm => [/andP [] | /eqP -> //].
by rewrite -eqn_leq => /eqP <- ->.
Qed.

Lemma avg_r a a' : a <= a' -> a <= (a + a')./2.
Proof.
move=> Haa'.
by rewrite -[X in X <= _]doubleK half_leq // -addnn leq_add2l.
Qed.

Lemma avg_l a a' : a <= a' -> (a + a')./2 <= a'.
Proof.
move=> Haa'.
rewrite -[X in _ <= X]doubleK.
apply half_leq.
by rewrite -addnn leq_add2r.
Qed.

Lemma avg_ltn_l a a' : a < a' -> (a+a')./2 < a'.
Proof.
move=> n.
destruct a'.
  by rewrite ltn0 in n.
refine (leq_ltn_trans _ (ltnSn _)).
rewrite -addSnnS.
case Haa': (a == a').
  by rewrite -(eqP Haa') -add1n -addnA addnn -/(true : nat) half_bit_double.
rewrite -[X in _ <= X]doubleK half_leq // -addnn leq_add2r.
by rewrite ltn_neqAle Haa' -ltnS.
Qed.

Lemma binarysearchE x :
  def > x.2 -> x.1 <= x.2 -> binarysearch x = Intervalsearch x.
Proof.
move: x.
refine (well_founded_ind well_founded_myltn _ _) => [] [a a'] /= IH Hdef Hx.
rewrite binarysearch_unfold /= /binarysearch' /=.
destruct Bool.bool_dec.
  have {Hx e}Haa': a = a'.
    move/andP: (conj Hx e).
    by rewrite -eqn_leq => /eqP.
  by rewrite Haa' Intervalsearch_one.
move/negP in n.
rewrite -ltnNge in n.
destruct Bool.bool_dec.
+ rewrite IH /=; first last.
  - by apply avg_r.
  - refine (leq_ltn_trans _ Hdef).
    by apply avg_l.
  - rewrite /myltn /=.
    apply /leP.
    by rewrite ltn_sub2r // avg_ltn_l.
  apply Intervalsearch_eq => //=.
  - by apply avg_r.
  - by apply avg_l.
  - move=> u /andP [e1].
    by rewrite ltnNge e1.
  - move=> u /andP [e1 _].
    by apply (leq_trans e), g_incr.
+ rewrite IH //=; first last.
   - by apply avg_ltn_l.
  - rewrite /myltn /=.
    apply /ltP.
    apply ltn_sub2l; first done.
    by rewrite ltnS avg_r.
  case Hi: (i <= g a'); first last.
    move/negP/negP in Hi.
    by rewrite !Intervalsearch_out.
  apply Intervalsearch_eq => //=.
  - by apply leqW, avg_r.
  - by apply avg_ltn_l.
  - move=> u /andP [_].
    rewrite ltnS.
    move/g_incr/leq_ltn_trans; apply.
    move/negP: n0.
    by rewrite -ltnNge.
  - move=> u.
    by rewrite -eqn_leq => /eqP <-.
Qed.

End binary_search.

Section bfs.

(* foldl-like arguments for bfs *)
Variable T : Type.
Variable A : eqType. (* label of tree *)
Variable f : T -> A -> T.

Definition qsize q := sumn (map (@number_of_nodes A) q).

Function bfs a q {measure qsize q} :=
  match q with
  | [::] => a
  | t :: q' =>
      let: Node v ts := t in
      bfs (f a v) (q' ++ ts)
  end.
Proof.
  move=> _ _ _ q' v ts _ _.
  apply/leP.
  by rewrite /qsize /= map_cat sumn_cat addnC ltn_add2r number_of_nodes_Node.
Qed.

Lemma bfs_level_order_forest_traversal' a q :
  bfs a q = foldl f a (flatten (forest_traversal (@label_of_node A) q)).
Proof.
  apply bfs_ind => {a q} // a q t q' Hq v ts Ht -> /=.
  case/boolP: (nilp q') => Hq'.
    by rewrite (nilP Hq').
  rewrite (forest_traversalE _ Hq') /=; congr foldl.
  rewrite /forest_traversal foldr_cat.
  set fts := foldr _ _ ts.
  rewrite (forest_traversalE' _ _ Hq') /= -catA; congr cat.
  case: fts => // h fts.
  rewrite [LHS]/= -!(foldr_map (level_traversal _) (mzip (cat_monoid A))).
  by rewrite -foldr1_mulr /flatten flatten_mzipC.
Qed.

End bfs.
