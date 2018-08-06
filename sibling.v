From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun bigop finset.

Require Import compact_data_structures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* tentative definition of the siblings of a node in a tree *)
(* NB: put the height of the tree in the type like in degree_profile? not sure...*)

(* trees with bounded branching, inspired from degree_profile.v *)
Fixpoint max_deg (A : Type) (t : tree A) : nat :=
  let: Node _ l := t in foldr maxn (size l) (map (@max_deg _) l).

Record btree (A : Type) n : Type := Btree {
  bt :> tree A;
  _ : max_deg bt <= n }.

From infotheo Require Import degree_profile. (* NB: only to have foldr_maxnE? *)

Section take_tree.

Variables (A : eqType) (n : nat).

Fixpoint take_tree (t : tree A) : tree A :=
  let: Node a l := t in let s := map take_tree l in Node a (take n s).

Lemma max_deg_take_tree (t : tree A) : max_deg (take_tree t) <= n.
Proof.
elim/tree_ind3: t => a l IH /=.
rewrite TreeEnsemble.foldr_maxnE (* TODO: move to infotheo/ssr_ext.v? *).
apply/andP; split.
- by rewrite size_take size_map; case: ifPn => //; rewrite -leqNgt.
- apply/allP => m /mapP [t /mem_take/mapP [t' Ht' ->{t} ->{m}]]; exact/IH.
Qed.

Lemma take_tree_id (t : tree A) (Ht : max_deg t <= n) : take_tree t = t.
Proof.
elim/tree_ind3: t Ht => a l IH.
rewrite /= TreeEnsemble.foldr_maxnE => /andP[ln /allP H].
rewrite -map_take take_oversize //; congr Node.
apply map_id_in => /= t tl.
apply/IH/H/mapP => //; by exists t.
Qed.

End take_tree.

Definition btree_decode (A : eqType) n (t : tree A) : btree A n :=
  Btree (@max_deg_take_tree _ n t).

Lemma cancel_btree (A : eqType) n : @cancel _ _ (@bt A n) (@btree_decode A n).
Proof.
case=> t Ht.
rewrite /btree_decode.
move: (max_deg_take_tree n t); rewrite (take_tree_id Ht) => ?.
congr Btree; exact: eq_irrelevance.
Qed.

Definition btree_eqMixin (A : eqType) n:= CanEqMixin (@cancel_btree A n).
Canonical btree_eqType (A : eqType) n := Eval hnf in EqType _ (@btree_eqMixin A n).

Definition btree_choiceMixin (A : choiceType) n := CanChoiceMixin (@cancel_btree A n).
Canonical btree_choiceType A n := Eval hnf in
      ChoiceType _ (btree_choiceMixin A n).

Definition btree_countMixin (A : countType) n := CanCountMixin (@cancel_btree A n).
Canonical btree_countType A n := Eval hnf in CountType _ (@btree_countMixin A n).

From infotheo Require Import ssr_ext. (* NB: to have bounded sequences *)

Program Definition pad_bseqR n (def : 'I_n.+1) l (s : l.-bseq 'I_n.+1) : l.-bseq 'I_n.+1 :=
  let: Bseq s' s'n := s in @Bseq _ _ (pad_seqR def s' l) _.
Next Obligation. by rewrite size_pad_seqR leqnn. Defined.

Lemma size_pad_bseqR n def l s : size (@pad_bseqR n def l s) = l.
Proof. by case: s => s Hs /=; rewrite size_pad_seqR. Qed.

Lemma pad_seqR_rcons (A : eqType) def (a : seq A) b n : size a <= n ->
  pad_seqR def (rcons a b) n.+1 = rcons a b ++ nseq (n - size a) def.
Proof. move=> am; by rewrite /pad_seqR size_rcons ltnS am. Qed.

Section position.

Variables (l : nat) (* intended to be the max depth *) (A : finType) (n : nat) (t : btree A n).

Record position := Position {
  pos :> l.-bseq 'I_n ;
  Hpos : valid_position t (map (@nat_of_ord n) pos)
}.

Canonical pos_subtype := [subType for pos].
Definition pos_eqMixin := Eval hnf in [eqMixin of position by <:].
Canonical pos_eqType := Eval hnf in EqType position pos_eqMixin.
Definition pos_choiceMixin := [choiceMixin of position by <:].
Canonical pos_choiceType := Eval hnf in ChoiceType position pos_choiceMixin.
Definition pos_countMixin := [countMixin of position by <:].
Canonical pos_countType := Eval hnf in CountType position pos_countMixin.
Canonical pos_subCountType := Eval hnf in [subCountType of position].
Definition pos_finMixin := [finMixin of position by <:].
Canonical pos_finType := Eval hnf in FinType position pos_finMixin.
Canonical poss_subFinType := Eval hnf in [subFinType of position].

End position.
Arguments Position [l] [A] [n] _ _.

Notation "l .-pos" := (@position l _ _) (at level 2, format "l .-pos") : type_scope.
Coercion pos_coercion l (A : finType) n (t : btree A n) (p : l.-pos t) : l.-bseq 'I_n :=
  @pos l A n t p.

Section position_prop.

Variable (A : finType).

Lemma size_position l n (t : btree A n) (p : l.-pos t) : size p <= l.
Proof. by case: p => -[]. Qed.

Definition positionnil l n (t : btree A n) : l.-pos t :=
  Position t (@bseq0 l _) erefl.

Lemma position_rconsP l n (t : btree A n) (p : l.+1.-pos t) :
  reflect
  (exists (a : l.-pos t) (b : 'I_n) H, p = Position _ [bseq of rcons a b] H)
  (p != positionnil l.+1 t).
Proof.
apply/(iffP idP) => [|[a [b [H pab]]]]; last first.
  apply/negP => /eqP/(congr1 (@pos _ _ _ _)); rewrite pab => -[] /(congr1 size).
  by rewrite size_rcons.
case: p => -[] [//| a b]; rewrite lastI => H1 H2 H3.
have H4 : size (belast a b) <= l.
  by rewrite {H2 H3}; rewrite size_rcons ltnS in H1.
have H5 : valid_position t (map (@nat_of_ord n) (belast a b)).
  apply (@valid_position_rcons _ _ _ (last a b)); by rewrite -map_rcons.
exists (Position t (Bseq H4) H5), (last a b), H2.
apply val_inj => /=; exact/val_inj.
Qed.

Definition position_take l n (t : btree A n) (k : nat)(p : l.-pos t) : l.-pos t.
apply: (Position t (bseq_take p k)).
abstract (by rewrite map_take (@valid_position_take _ t _ _ (Hpos p))).
Defined.

End position_prop.

From infotheo Require Import kraft. (* NB: to have ary_of_nat *)

Lemma poly_lt a a' b b' k :
  a < k ->
  a >= a' ->
  b < b' ->
  a' + k * b' > a + k * b.
Proof.
move=> Hak Haa' Hbb'.
have [b'' Hb''] : exists b'', b' = 1 + b''.
 exists b'.-1; rewrite add1n prednK //; by case: b' Hbb'.
subst b'.
rewrite mulnDr muln1 addnA.
rewrite -ltn_subRL addnC -addnBA; last first.
  by rewrite (@leq_trans k) // ?leq_addl //  ltnW.
rewrite -(@prednK (_ - _)); last by rewrite subn_gt0 ltn_addl.
by rewrite -addSnnS ltn_addr // ltnS leq_pmul2l // (leq_ltn_trans _ Hak).
Qed.

Section lexicographic_product.

Variables (A B : eqType) (ltA : A -> A -> bool) (ltB : B -> B -> bool).

Definition lexprod : A * B -> A * B -> bool := fun ab ab' =>
  let: (a, b) := ab in let: (a', b') := ab' in
  (ltA a a') || (a == a') && ltB b b'.

Lemma lexprod_trans (ltA_trans : transitive ltA) (ltB_trans : transitive ltB) :
  transitive lexprod.
Proof.
move=> [a1 a2] [b1 b2] [c1 c2] /=.
case/orP => [ba1|].
  case/orP => [ac1|]; first by rewrite (@ltA_trans _ _ _ ba1 ac1).
  case/andP => /eqP <-{c1}; by rewrite ba1.
case/andP => /eqP ->{b1} ba2 /orP[ac1|]; first by rewrite ac1.
case/andP => /eqP <-{c1} ac2; by rewrite (@ltB_trans _ _ _ ba2 ac2) eqxx orbT.
Qed.

Hypothesis wfA : well_founded ltA.
Hypothesis wfB : well_founded ltB.

Lemma wflexprod : well_founded lexprod.
Proof.
case=> a0 b0; move: b0.
set P := fun a => forall b, Acc lexprod (a, b).
apply (Init.Wf.well_founded_induction wfA P) => a Ha.
rewrite /P.
set Q := fun b => Acc lexprod (a, b).
apply (Init.Wf.well_founded_induction wfB Q) => b Hb.
rewrite /Q.
by apply Acc_intro => -[a' b'] /orP[/(Ha a')//|/andP[/eqP -> /(Hb b')]].
Qed.

End lexicographic_product.

(*NB(rei): proof recycled from seplog, needs to be cleaned*)
Section total_order_facts.

Variable A : eqType.
Variable ltA : A -> A -> bool.
Notation "x < y" := (ltA x y).
Variable ltA_total : forall m n, (m != n) = (m < n) || (n < m).

Lemma tri' a b : a < b \/ a = b \/ b < a.
Proof.
case/boolP : (a == b).
- move/eqP; auto.
- rewrite ltA_total; case/orP; auto.
Qed.

Lemma tri n n' : n' < n -> forall a, a < n' \/ a = n' \/ n' < a /\ a < n \/ a = n \/ n < a.
Proof.
move=> H a.
case/boolP : (a == n').
- move/eqP; auto.
- rewrite ltA_total. case/orP; auto.
  move: (tri' a n); case; auto.
Qed.

End total_order_facts.

Section lexicographic_products.

Fixpoint lex n (s s' : seq 'I_n) := (* NB: same def as in seplog *)
  match s, s' with
  | [::]  , [::]   => false
  | [::]  , _ :: _ => true
  | _ :: _, [::]   => false
  | a :: b, c :: d => if a < c then true else
                      if a == c then lex b d else
                      false
  end.

Lemma lexss n (s : seq 'I_n) : lex s s = false.
Proof. by elim: s => // h t IH /=; rewrite ltnn eqxx. Qed.

Lemma lex_cons n a (t1 t2 : seq 'I_n) : lex (a :: t1) (a :: t2) = lex t1 t2.
Proof. by rewrite /= ltnn eqxx. Qed.

Lemma lex_cons_neq n (a b : 'I_n) t1 t2 : a < b -> lex (a :: t1) (b :: t2).
Proof. by move=> ab /=; rewrite ab. Qed.

Lemma lex_cat n s (t1 t2 : seq 'I_n) : lex (s ++ t1) (s ++ t2) = lex t1 t2.
Proof. by elim: s t1 t2 => // a b IH t1 t2; rewrite 2!cat_cons lex_cons IH. Qed.

Lemma lex_catl n (s t1 t2 : seq 'I_n) : size t1 = size t2 ->
  lex (t1 ++ s) (t2 ++ s) = lex t1 t2.
Proof.
elim: t1 t2 s => [t2 s /eqP|a b IH [//|c d] s [bd] /=].
- by rewrite eq_sym size_eq0 => /eqP -> /=; rewrite lexss.
- by case: ifPn => ac //; case: ifPn => // ac'; rewrite IH.
Qed.

Lemma prefix_lex n (s t : seq 'I_n) : prefix s t -> size s < size t -> lex s t.
Proof.
elim: s t => [[]//|h1 t1 IH [//|h2 t2]].
rewrite prefix_cons => /andP[/eqP-> /=]; rewrite ltnn eqxx ltnS; exact: IH.
Qed.

Lemma lexs0 n (s : seq 'I_n.+1) l : size s = l -> lex s (nseq l ord0) = false.
Proof.
elim: l s => [|l IH [//|h t] /= [lt]]; first by case.
by case: ifPn => //; rewrite IH.
Qed.

Lemma lex_neq n (t1 t2 : seq 'I_n) : lex t1 t2 -> t1 != t2.
Proof. apply: contraTN => /eqP ->; by rewrite lexss. Qed.

Lemma lexP n (p q : seq 'I_n.+1) : size q = size p ->
  lex q p <-> exists k, [&& k.+1 <= size p, take k q == take k p & nth ord0 q k < nth ord0 p k].
Proof.
move=> qp; split; move: qp.
- move Hl : (size p) => l.
  elim: l p q Hl => [[|//] [|] //|l IH].
  case=> // p1 p2 [] // q1 q2 [Hp2] [Hq2].
  rewrite [lex _ _]/=; case: ifPn => [qp1 _|qp1]; first by exists O.
  case: ifPn => [/eqP{qp1} ->{q1} H|//].
  case: (IH _ _ Hp2 Hq2 H) => k /and3P[kl /eqP H1 H2].
  by exists k.+1; rewrite ltnS kl /= H1 H2 eqxx.
- move Hl : (size p) => l.
  elim: l p q Hl => [[|//] [|] // _ _ [k []] //|l IH].
  case=> // p1 p2 [] // q1 q2 [Hp2] [Hq2].
  case=> k /and3P[kl /eqP H1 H2].
  case: k kl H1 H2 => [_ _|k kl [->{q1} H1 /= H2]] /=; first by move=> ->.
  rewrite ltnS in kl.
  rewrite ltnn eqxx IH //; by exists k; rewrite kl /= H1 eqxx.
Qed.

(* TOOD(rei): move? *)
Lemma neq_ltn_for_ordinal l (m n : 'I_l) : (m != n) = (m < n) || (n < m).
Proof. exact: neq_ltn. Qed.

(*NB(rei): proof recycled from seplog, needs to be cleaned*)
Lemma lex_trans l m n : forall p : seq 'I_l, lex m n -> lex n p -> lex m p.
Proof.
move: m n; elim.
- case=> //. move=> n0 n. by case.
- move=> n0 n Hn m; move: m n0 n Hn. elim=> //.
  move=> m0 m Hm n0 n Hn p; move: p m0 m Hm n0 n Hn. elim=> //.
  move=> p0 p Hp  m0 m Hm n0 n Hn /=.
  move=> Hnm Hmp.
  have [H1 | [H1 | H1] ] : n0 < p0 \/ n0 = p0 \/ p0 < n0 by apply (tri' (@neq_ltn_for_ordinal l)).
  + rewrite H1 //.
  + subst p0.
    rewrite ltnn eq_refl.
    have [H2 | [H2 | H2] ] : n0 < m0 \/ n0 = m0 \/ m0 < n0 by apply (tri' (@neq_ltn_for_ordinal l)).
    * have H3 : m0 < n0 = false.
        apply/negP => H'. move: (ltn_trans H2 H') => H''. rewrite ltnn // in H''.
      rewrite H3 in Hmp.
      have H4 : m0 == n0 = false.
        apply/eqP. move=> H'; subst. rewrite H2 // in H3.
      rewrite H4 // in Hmp.
    * subst m0.
      rewrite ltnn eq_refl in Hnm.
      rewrite ltnn eq_refl in Hmp.
      by apply Hn with m.
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltn_trans H2 H') => H''. rewrite ltnn // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H2 // in H3.
      rewrite H4 // in Hnm.
  + move: (tri (@neq_ltn_for_ordinal l) H1 m0) => [ H2 | [ H2 | [ [H2 H2'] | [ H2 | H2 ] ] ] ].
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltn_trans (ltn_trans H1 H') H2) => H''. rewrite ltnn // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite (ltn_trans H2 H1) // in H3.
      rewrite H4 // in Hnm.
    * subst p0.
      rewrite ltnn eq_refl in Hmp.
      have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltn_trans H1 H') => H''. rewrite ltnn // in H''.
      rewrite H3 in Hnm.
      have H4 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H1 // in H3.
      rewrite H4 // in Hnm.
    * have H3 : n0 < m0 = false.
        apply/negP => H'. move: (ltn_trans H' H2') => H''. rewrite ltnn // in H''.
      rewrite H3 in Hnm.
      have H6 : n0 == m0 = false.
        apply/eqP. move=> H'; subst. rewrite H2' // in H3.
      rewrite H6 // in Hnm.
    * subst n0.
      rewrite ltnn eq_refl in Hnm.
      have H3 : m0 < p0 = false.
        apply/negP => H'. move: (ltn_trans H1 H') => H''. rewrite ltnn // in H''.
      rewrite H3.
      rewrite H3 in Hmp.
      have H4 : m0 == p0 = false.
        apply/eqP. move=> H'; subst. rewrite H1 // in H3.
      rewrite H4 // in Hmp.
    * have H3 : n0 < p0 = false.
        apply/negP => H'. move: (ltn_trans H1 H') => H''. rewrite ltnn // in H''.
      rewrite H3.
      have H4 : m0 < p0 = false.
        apply/negP => H'. move: (ltn_trans H1 (ltn_trans H2 H')) => H''. rewrite ltnn // in H''.
      rewrite H4 in Hmp.
      have H5 : m0 == p0 = false.
        apply/eqP. move=> H'; subst. rewrite (ltn_trans H1 H2) // in H4.
      rewrite H5 // in Hmp.
Qed.

Lemma lex_nat_of_ary n (def := ord0) l (x y : l.-bseq 'I_n.+2) :
  lex (pad_bseqR def x) (pad_bseqR def y) ->
  nat_of_ary x * n.+2 ^ (l - size x) < nat_of_ary y * n.+2 ^ (l - size y).
Proof.
elim: l x y => [|l IH]; first by case; case => // ?; case; case.
case=> x Hx; case=> y Hy /=.
rewrite /pad_seqR Hx Hy.
destruct x as [|x1 x2]; [rewrite {Hx}|rewrite /= ltnS in Hx].
  rewrite cat0s nat_of_ary_nil mul0n subn0.
  destruct y as [|y1 y2]; [by rewrite cat0s lexss|rewrite /= ltnS in Hy].
  rewrite (_ : nseq _ _ = def :: nseq l def) //=.
  case: ifPn => [y10 _|].
    rewrite muln_gt0 expn_gt0 /= andbT lt0n nat_of_ary_0 /= negb_and eq_sym.
    apply/orP; left; apply: contraTN y10 => /eqP <-; by rewrite ltnn.
  rewrite -leqNgt leq_eqVlt => /orP[] y1def; last first.
    rewrite ifF //; by apply/negbTE; apply: contraTN y1def => /eqP ->; rewrite ltnn.
  rewrite ifT //; last by rewrite eq_sym; apply: contraTT y1def.
  rewrite subSS => H.
  set h1 := Bseq (eq_leq (size_nseq l def)).
  set h2 := Bseq Hy.
  move: (IH h1 h2).
  rewrite [X in lex X _](_ : _ = nseq l def); last first.
    by rewrite /h1 /= pad_seqR_size // size_nseq.
  rewrite [X in lex _ X](_ : _ = y2 ++ nseq (l - size y2) def); last first.
    by rewrite /pad_bseqR /= /pad_seqR Hy.
  move/(_ H).
  rewrite [in X in _ < X -> _]/= => K.
  by rewrite -cat1s nat_of_ary_cat mulnDl addn_gt0 (leq_ltn_trans _ K) // orbT.
destruct y as [|y1 y2]; [|rewrite /= ltnS in Hy].
  rewrite cat0s subn0 nat_of_ary_nil mul0n ltn0.
  by rewrite lexs0 // size_cat size_nseq addnBA // addnC addnK.
rewrite /=.
case: ifPn => [x1y1 _|].
  rewrite -cat1s -(cat1s y1) 2!nat_of_ary_cat card_ord 2!nat_of_ary1.
  rewrite !mulnDl !subSS -!mulnA -!expnD !subnKC //.
  case/boolP : (nat_of_ary y2 * n.+2 ^ (l - size y2) <= nat_of_ary x2 * n.+2 ^ (l - size x2)) => H.
    rewrite addnC [in X in _ < X]addnC (mulnC x1) (mulnC y1) poly_lt //.
    by rewrite -{2}(subnKC Hx) expnD ltn_pmul2r // ?expn_gt0 // nat_of_ary_ub.
  rewrite -ltnNge in H.
  rewrite -ltn_subRL (leq_trans H) // addnC -addnBA ?leq_addr //.
  by rewrite leq_pmul2r // ?expn_gt0 // ltnW.
rewrite -leqNgt => y1x1.
case: ifPn => // {y1x1}y1x1.
rewrite (eqP y1x1) !subSS => H.
move: (IH (Bseq Hx) (Bseq Hy)).
rewrite [X in lex X _](_ : _ = x2 ++ nseq (l - size x2) def); last first.
  by rewrite /pad_bseqR /= /pad_seqR Hx.
rewrite [X in lex _ X](_ : _ = y2 ++ nseq (l - size y2) def); last first.
  by rewrite /pad_bseqR /= /pad_seqR Hy.
move/(_ H) => /= K.
rewrite -cat1s nat_of_ary_cat -[in X in _ < X]cat1s nat_of_ary_cat card_ord.
by rewrite 2!mulnDl -!mulnA -!expnD !subnKC // ltn_add2l.
Qed.

End lexicographic_products.

Require Import Wellfounded.Inverse_Image.

Section lexicographic_order.

Variables (A B : eqType) (l : nat) (ltA : l.-bseq A -> l.-bseq A -> bool).

Definition lexord : l.-bseq A -> l.-bseq A -> bool := fun a a' =>
  lexprod ltn ltA (size a, a) (size a', a').

Lemma lexord_trans (ltA_trans : transitive ltA) : transitive lexord.
Proof. move=> ? ? ?; exact: (lexprod_trans ltn_trans ltA_trans). Qed.

Hypothesis wfA : well_founded ltA.

Lemma wflexord : well_founded lexord.
Proof.
rewrite /lexord.
have H : well_founded (fun x x0 : nat_eqType => ltn x x0).
  by apply: (@Wf_nat.well_founded_lt_compat _ id) => x y /ltP.
move: (wflexprod H wfA) => {H}H.
by move: (wf_inverse_image _ _ _ (fun s : l.-bseq A => (size s, s)) H).
Qed.

End lexicographic_order.

Section lex_bseq.

Definition lex_bseq n def l (s s' : l.-bseq 'I_n.+1) :=
  lex (pad_bseqR def s) (pad_bseqR def s').

Lemma lex_bseq_trans l n def : transitive (@lex_bseq n def l).
Proof. move=> a b c; exact: lex_trans. Qed.

Lemma wf_lex_bseq n l : well_founded (@lex_bseq n.+1 ord0 l).
Proof.
apply (Wf_nat.well_founded_lt_compat _
  (fun x : l.-bseq 'I_n.+2 => (@nat_of_ary n) (pad_seqR ord0 x l))) => x y.
rewrite /lex_bseq => xy.
rewrite /pad_seqR 2!size_bseq 2!nat_of_ary_cat; apply/ltP.
rewrite 2!size_nseq 2!nat_of_ary_nseq0 2!addn0 card_ord.
exact: lex_nat_of_ary.
Qed.

Definition blex n def l := lexord (@lex_bseq n def l).

Lemma blex_bseq0 n l (p : l.-bseq 'I_n.+1) : blex ord0 p (bseq0 l 'I_n.+1) = false.
Proof.
apply/negbTE.
rewrite /blex /lexord /lexprod /= negb_and.
case/boolP : (size p == 0) => //=.
rewrite size_eq0 => /eqP p0.
destruct p as [p Hp]; simpl in *.
by rewrite /lex_bseq /= /pad_bseqR /pad_seqR /= Hp p0 !subn0 cat0s lexss.
Qed.

Lemma wf_blex n l : well_founded (@blex n.+1 ord0 l).
Proof. exact/wflexord/wf_lex_bseq. Qed.

Lemma blex_trans l n : transitive (@blex n.+1 ord0 l).
Proof. exact/lexord_trans/lex_bseq_trans. Qed.

End lex_bseq.

Section order_ind.

Variables (n : nat).

Lemma bseq_ind : forall (P : forall l, l.-bseq 'I_n.+2 -> Set),
  (forall l (x : l.-bseq 'I_n.+2),
    (forall (y : l.-bseq 'I_n.+2), blex ord0 y x -> P _ y) -> P _ x) ->
  forall l (a : l.-bseq 'I_n.+2), P _ a.
Proof.
move=> P H l p.
pose Q : seq 'I_n.+2 -> Set := fun s =>
  match Bool.bool_dec (size s <= l) true with
  left H => P _ (Bseq H) | _ => False end.
have K : forall x : l.-bseq 'I_n.+2,
    (forall y : l.-bseq 'I_n.+2, blex ord0 y x -> Q y) -> Q x.
  move=> x Hx; rewrite /Q; case: Bool.bool_dec => xl; last first.
    destruct x as [x xH].
    simpl in xl.
    by rewrite xH in xl.
  apply H => -[y Hy] /=.
  rewrite (_ : Bseq xl = x); last first.
  destruct x; last exact: val_inj.
  move/(Hx (Bseq Hy)); rewrite /Q.
  case: Bool.bool_dec => yl; last tauto.
  by rewrite (eq_irrelevance yl Hy).
move: (Init.Wf.well_founded_induction (@wf_blex _ l) Q K p); rewrite /Q.
case: Bool.bool_dec => // pl.
destruct p as [p Hp].
by rewrite (eq_irrelevance Hp pl).
Qed.

Variable A : finType.
Variable t : btree A n.+2.

Lemma pos_ind : forall (P : forall l, l.-pos t -> Set),
  (forall l (x : l.-pos t),
    (forall y : l.-pos t, blex ord0 y x -> P _ y) -> P _ x) ->
  forall l (a : l.-pos t), P _ a.
Proof.
move=> P H l [p Hp].
pose Q : forall l, l.-bseq 'I_n.+2 -> Set := fun l s =>
  match Bool.bool_dec (valid_position t (map (@nat_of_ord _) s)) true with
  left H => P _ (Position _ _ H) | _ => True end.
have K : forall l (x : l.-bseq 'I_n.+2),
    (forall y : l.-bseq 'I_n.+2, blex ord0 y x -> Q _ y) -> Q _ x.
  move=> l' x Hx; rewrite /Q; case: Bool.bool_dec => xl; last exact I.
  apply H => -[y Hy] /= /Hx; rewrite /Q.
  case: Bool.bool_dec => yl; [ | tauto].
  by rewrite (eq_irrelevance yl Hy).
move: (@bseq_ind Q K _ p); rewrite /Q.
case: Bool.bool_dec => // pl.
by rewrite (eq_irrelevance Hp pl).
Qed.

End order_ind.

Section sibling_ancestors.

Variables (A : finType) (n : nat) (t : btree A n.+1) (l : nat).
Hypothesis tl : height t <= l.

Definition sibling (p : l.-pos t) : {set l.-pos t} :=
  if p == [::] :> seq _ then set0 else [set q : l.-pos t |
    [&& q != [::] :> seq _, belast ord0 p == belast ord0 q & q != p]].

Lemma siblingE (p : l.-pos t) r : r \in sibling p =
  [&& p != [::] :> seq _, r != [::] :> seq _, belast ord0 p == belast ord0 r & r != p].
Proof.
apply/idP/idP; last by case/and4P=>H K L ?; rewrite /sibling (negbTE H) inE K L.
rewrite /sibling; case: ifPn => [|p0]; by [rewrite in_set0|rewrite inE].
Qed.

Lemma sibling_nil : sibling (positionnil l t) = set0. Proof. by []. Qed.

Lemma siblingC (p : l.-pos t) r : (p \in sibling r) = (r \in sibling p).
Proof.
rewrite /sibling; case: ifPn => [/eqP|] r0.
  rewrite in_set0; apply/esym/negbTE.
  case: ifPn => [|p0]; by [rewrite in_set0|rewrite inE negb_and negbK r0 eqxx].
rewrite inE; case: ifPn => [|/= p0]; by
  [rewrite in_set0 | rewrite inE r0 /= (eq_sym p) eq_sym].
Qed.

Lemma sibling_size p q : q \in sibling p -> size q = size p.
Proof.
move: p q => -[[p Hp] Kp] [[q Hq] Kq] //= H; move: (H).
rewrite siblingC siblingE => /and4P[p0 q0 pq qp].
destruct p as [|p1 p2] => //; simpl in *.
destruct q as [|q1 q2] => //; simpl in *.
move/eqP: pq => /(congr1 size); by rewrite /= 2!size_belast.
Qed.

Lemma sibling_neq p q : q \in sibling p -> q != p.
Proof. by rewrite siblingE => /and4P[_ _ /eqP]. Qed.

Lemma sibling_belast p q : q \in sibling p -> belast ord0 p = belast ord0 p.
Proof. by rewrite siblingE => /and4P[_ /eqP]. Qed.

Definition lsibling (p : l.-pos t) : {set l.-pos t} :=
  sibling p :&: [set q : l.-pos t | last ord0 q < last ord0 p ].

Lemma lsibling_nil : lsibling (positionnil l t) = set0.
Proof. by rewrite /lsibling sibling_nil set0I. Qed.

Definition rsibling (p : l.-pos t) : {set l.-pos t} :=
  sibling p :&: [set q : l.-pos t | last ord0 p < last ord0 q ].

Lemma siblingU (p : l.-pos t) : sibling p = lsibling p :|: rsibling p.
Proof.
apply/setP => /= q; rewrite !inE -andb_orr; apply/idP/idP => [H|/andP[] //].
rewrite H /=; move: (leq_total (last ord0 p) (last ord0 q)).
rewrite leq_eqVlt orbAC leq_eqVlt eq_sym orbA orbb -orbA => /orP[K|//].
exfalso; move: H; rewrite siblingE => /and4P[p0 q0 /eqP pq /eqP]; apply.
destruct p as [[[|p1 p2] Hp] Kp] => //; simpl in *.
destruct q as [[[|q1 q2] Hq] Kq] => //; simpl in *.
apply/val_inj/val_inj => /=; rewrite 2!lastI; congr rcons; last exact/eqP.
by case: pq.
Qed.

Lemma siblingI (p : l.-pos t) : [disjoint lsibling p & rsibling p].
Proof.
rewrite -setI_eq0; apply/eqP/setP => /= q; rewrite !inE; apply/negbTE.
by rewrite !negb_and orbAC orbA orbb -orbA -!leqNgt leq_total orbT.
Qed.

Definition ancestors (p : l.-pos t) : {set l.-pos t} :=
  [set q : l.-pos t | (prefix q p) && (size q < size p)].

Lemma ancestors_nil : ancestors (positionnil l t) = set0.
Proof. apply/setP => p; by rewrite !inE /= prefix_nil ltn0 andbF. Qed.

Lemma ancestorsIsibling (p : l.-pos t) :
  [disjoint \bigcup_(q in ancestors p) (q |: sibling q) & sibling p].
Proof.
rewrite -setI_eq0; apply/set0Pn => -[/= q]; rewrite in_setI => /andP[].
case/bigcupP => r; rewrite inE => /andP[rp pr]; rewrite 2!inE => /orP[/eqP ->|].
- move/sibling_size /eqP; by rewrite (ltn_eqF pr).
- move/sibling_size => qr /sibling_size /eqP; by rewrite qr (ltn_eqF pr).
Qed.

Lemma ancestorsIlsibling (p : l.-pos t) :
  [disjoint \bigcup_(q in ancestors p) (q |: sibling q) & lsibling p].
Proof.
move: (ancestorsIsibling p); rewrite siblingU -setI_eq0.
by rewrite setIUr setU_eq0 2!setI_eq0 => /andP[].
Qed.

Lemma ancestorsIrsibling (p : l.-pos t) :
  [disjoint \bigcup_(q in ancestors p) (q |: sibling q) & rsibling p].
Proof.
move: (ancestorsIsibling p); rewrite siblingU -setI_eq0.
by rewrite setIUr setU_eq0 2!setI_eq0 => /andP[].
Qed.

Lemma ancestorsIself (p : l.-pos t) :
  [disjoint \bigcup_(i in ancestors p) (i |: sibling i) & [set p]].
Proof.
rewrite -setI_eq0; apply/eqP/setP => /= q; rewrite in_set0; apply/negbTE.
rewrite !inE negb_and; case/boolP : (q == p) => [/eqP ->|]; last by rewrite orbT.
rewrite {q} orbF; apply/bigcupP => -[/= q]; rewrite inE => /andP[qp pq].
rewrite !inE => /orP[|].
  by apply/negP; apply: contraTN pq => /eqP ->; rewrite ltnn.
rewrite siblingE => /and4P[q0 p0 /eqP].
destruct p as [[[|p1 p2] Hp] Kp] => //; simpl in *.
destruct q as [[[|q1 q2] Hq] Kq] => //; simpl in *.
rewrite {q0 p0} => -[qp1l] /eqP; apply.
apply/val_inj/val_inj => /=.
move: qp; rewrite !lastI prefix_rcons qp1l => /orP[H|/eqP //].
by exfalso; move: H => /prefix_leq_size; rewrite size_rcons ltnn.
Qed.

Definition generation (p : l.-pos t) : {set l.-pos t} :=
  [set q : l.-pos t | size q == size p].

Lemma generation_position_take (p q : l.-pos t) :
  size q < size p -> q \in generation (position_take (size q) p).
Proof. by move=> qp; rewrite inE /= size_take qp. Qed.

Definition lgeneration (p : l.-pos t) : {set l.-pos t} :=
  generation p :&: [set q : l.-pos t |
    [exists k : 'I_(size p), (take k p == take k q) && (nth ord0 q k < nth ord0 p k)] ].

Definition rgeneration (p : l.-pos t) : {set l.-pos t} :=
  generation p :&: [set q : l.-pos t |
    [exists k : 'I_(size p), (take k p == take k q) && (nth ord0 p k < nth ord0 q k)] ].

End sibling_ancestors.

Definition bseqW l (A : eqType) (t : l.-bseq A) : l.+1.-bseq A.
Proof. apply: (@Bseq _ _ t); by rewrite ltnW // ltnS size_bseq. Defined.

Lemma bseqW_inj l (A : eqType) : injective (@bseqW l A).
Proof. move=> -[a Ha] [b Hb] /= [ab]; exact/val_inj. Qed.

Definition posW l (A : finType) n (t : btree A n) (p : l.-pos t) : l.+1.-pos t :=
  Position t (bseqW (pos p)) (Hpos p).
Arguments posW [l] [A] [n] _.

Lemma posW_inj (A : finType) n (t : btree A n) l : injective (@posW l _ _ t).
Proof. move=> -[[a Ka] Ha] [[b Kb] Hb] /= [ab]; exact/val_inj/val_inj. Qed.

Definition bseqS l (A : finType) (t : l.+1.-bseq A) (Ht : size t <= l) : l.-bseq A :=
  Bseq Ht.

Definition posS l (A : finType) n (t : btree A n) (p : l.+1.-pos t) (Hp : size p <= l) : l.-pos t :=
  Position _ (bseqS Hp) (Hpos p).

Lemma ancestors_posW (A : finType) n (t : btree A n.+1) l (p : l.-pos _) :
  ancestors (posW t p) = posW t @: ancestors p.
Proof.
apply/setP => /= q; rewrite !inE; apply/idP/idP.
  case/andP => H1 H2; apply/imsetP.
  have ql : size q <= l by rewrite (leq_trans _ (size_bseq p)) // prefix_leq_size.
  exists (posS ql); [by rewrite inE /= H1 | exact/val_inj/val_inj].
case/imsetP => /= r Hr ->{q} /=; by rewrite inE in Hr.
Qed.

Lemma ancestors_rcons (A : finType) n (t : btree A n.+1) l (a : l.-pos _) (b : _) H H1 :
  ancestors (Position t [bseq of rcons a b] H) =
  posW t @: (ancestors (Position t a H1) :|: set1 a).
Proof.
rewrite /ancestors; apply/setP => /= p.
rewrite inE size_rcons ltnS.
apply/idP/idP => [/andP[pab pa]|].
  have pl : size p <= l by exact/(leq_trans pa)/size_position.
  apply/imsetP.
  exists (posS pl); last by rewrite /posW /posS /=; apply/val_inj/val_inj.
  rewrite inE in_set1.
  move: pab; rewrite prefix_rcons => /orP[|] pab; last first.
    by rewrite (eqP pab) size_rcons ltnn in pa.
  move: pa; rewrite leq_eqVlt => /orP[/eqP|] pa.
    apply/orP; right; apply/eqP/val_inj/val_inj => /=.
    by rewrite (prefix_same_size pab pa).
  by rewrite !inE pab pa.
case/imsetP => p'.
rewrite inE => /orP[|]; last first.
  rewrite in_set1 => /eqP -> /= ->.
  by rewrite leqnn andbT prefix_rcons prefix_refl.
rewrite inE prefix_rcons andb_orl => /andP[pa pa_size].
move=> ->; by rewrite pa /= (ltnW pa_size).
Qed.

Lemma sibling_posW (A : finType) n (t : btree A n.+1) l (p : l.-pos _) :
  sibling (posW t p) = posW t @: sibling p.
Proof.
apply/setP => q; apply/idP/idP => [H|]; last first.
  case/imsetP=> r rp ->{q}; by move: rp; rewrite !siblingE.
apply/imsetP.
have ql : size q <= l by rewrite (sibling_size H) /= size_bseq.
exists (posS ql); last exact/val_inj/val_inj.
move: H; by rewrite !siblingE.
Qed.

Lemma lsibling_posW (A : finType) n (t : btree A n.+1) l (p : l.-pos _) :
  lsibling (posW t p) = posW t @: lsibling p.
Proof.
apply/setP => q.
rewrite /lsibling sibling_posW imsetI; last by move => *; exact: posW_inj.
rewrite !inE; apply/idP/idP; case/andP => H1 H2; rewrite H1 /=.
  move: (H1) => /imsetP[q' H1' H1''].
  by apply/imsetP; exists q' => //; rewrite inE (leq_trans _ H2) // H1''.
move: (H2) => /imsetP[q' H2' H2'']; rewrite inE in H2'; by rewrite H2''.
Qed.

Lemma rsibling_posW (A : finType) n (t : btree A n.+1) l (p : l.-pos _) :
  rsibling (posW t p) = posW t @: rsibling p.
Proof.
apply/setP => q.
rewrite /rsibling sibling_posW imsetI; last by move => *; exact: posW_inj.
rewrite !inE; apply/idP/idP; case/andP => H1 H2; rewrite H1 /=.
  move: (H1) => /imsetP[q' H1' H1''].
  apply/imsetP; exists q' => //; rewrite inE; by rewrite H1'' in H2.
move: (H2) => /imsetP[q' H2' H2'']; rewrite inE in H2'; by rewrite H2''.
Qed.

Lemma blexE (A : finType) (n : nat) (t : btree A n.+1) l (p q : l.-pos t) :
  blex ord0 q p = (size q < size p) || (size q == size p) && lex_bseq ord0 q p.
Proof. by []. Qed.

Require Import rank_select louds.

Lemma rcons_decompose (A : finType) l n (t : btree A n.+1)
  (p : l.+1.-pos t) (a : l.-pos t) (b : 'I_n.+1) ab :
  p = Position t [bseq of rcons a b] ab ->
  #|\bigcup_(q in ancestors p) (q |: sibling q)| =
  #|\bigcup_(q in ancestors a) (q |: sibling q)| + #|lsibling a| + #|rsibling a|.+1.
Proof.
move=> ->.
rewrite ancestors_rcons => [|Hyp0].
  rewrite map_rcons in ab; exact: (valid_position_rcons ab).
rewrite big_imset /=; last by move=> *; exact: posW_inj.
rewrite bigcup_setU cardsU disjoint_setI0 ?cards0 ?subn0; last first.
  rewrite -setI_eq0 big_distrr /= (big_pred1 a); last by move=> /= ?; rewrite inE.
  rewrite setIUr setUC disjoint_setI0; last first.
    rewrite (eq_bigr (fun i => posW t @: (i |: sibling i))); last first.
      by move=> *; rewrite imsetU1 sibling_posW.
    rewrite -(@big_morph _ _ _ _ _ set0 _ (imsetU (posW t))) ?imset0 //.
    rewrite -setI_eq0 sibling_posW -imsetI; last by move=> *; exact: posW_inj.
    by rewrite imset_eq0 setI_eq0 ancestorsIsibling.
  rewrite set0U (eq_bigr (fun i => posW t @: (i |: sibling i))); last first.
    by move=> *; rewrite imsetU1 sibling_posW.
  rewrite -(@big_morph _ _ _ _ _ set0 _ (imsetU (posW t))) ?imset0 //.
  rewrite -imset_set1 -imsetI; last by move=> *; exact: posW_inj.
  by rewrite imset_eq0 setI_eq0 ancestorsIself.
rewrite -addnA; congr addn.
  rewrite -[RHS](card_imset _ (@posW_inj _ _ t _)); apply eq_card => /= q.
  rewrite (eq_bigr (fun i => posW t @: (i |: sibling i))); last first.
    by move=> *; rewrite imsetU1 sibling_posW.
  by rewrite -(@big_morph _ _ _ _ _ set0 _ (imsetU (posW t))) ?imset0.
rewrite (big_pred1 a); last by move=> /= ?; rewrite inE.
rewrite cardsU1 {2}siblingU cardsU disjoint_setI0 ?siblingI // cards0 subn0.
rewrite addnC addnS -[in RHS]addn1; congr addn.
  rewrite lsibling_posW card_in_imset; last by move=> *; exact: posW_inj.
  rewrite rsibling_posW card_in_imset //; by move=> *; exact: posW_inj.
by rewrite siblingE !eqxx /= !andbF.
Qed.

Lemma posW_decompose (A : finType) l n (t : btree A n.+1) (a : l.-pos t) :
  #|\bigcup_(q in ancestors a) (q |: sibling q)| + #|lsibling a| =
  #|\bigcup_(q in ancestors (posW t a)) (q |: sibling q)| + #|lsibling (posW t a)|.
Proof.
rewrite lsibling_posW card_in_imset; last by move=> *; exact: posW_inj.
rewrite ancestors_posW big_imset /=; last by move=> *; exact: posW_inj.
rewrite (eq_bigr (fun i => posW t @: (i |: sibling i))); last first.
  by move=> *; rewrite imsetU1 sibling_posW.
rewrite -(@big_morph _ _ _ _ _ set0 _ (imsetU (posW t))) ?imset0 //.
by rewrite card_in_imset; last by move=> *; exact: posW_inj.
Qed.

Require Import pred_succ.

Module louds_tentative.
  Section LOUDS_position.

Variable (A : finType) (n : nat) (t : btree A n.+2).

Definition children_of_pos l (p : l.-pos t) : nat :=
  children t (map (@nat_of_ord _) p).

Definition LOUDSpos_of_pos l (p : l.-pos t) :=
  (\sum_(x : l.-pos t| blex ord0 x p) (children_of_pos x).+1).+2.

Lemma predsE l (p : l.-pos t) : [set x : l.-pos t | blex ord0 x p] =
  (\bigcup_(q in ancestors p) (q |: generation q)) :|: lgeneration p.
Proof.
apply/setP => /= q; apply/idP/idP.
  rewrite inE blexE => /orP[qp|].
    rewrite inE; apply/orP; left; apply/bigcupP => /=.
    exists (position_take (size q) p).
      by rewrite inE /= size_take qp qp andbT prefix_take.
    rewrite in_setU1.
    case/boolP : (q == position_take (size q) p) => pq //=.
    by rewrite generation_position_take.
  case/andP => /eqP size_qp /lexP.
  rewrite 2!size_pad_bseqR => /(_ erefl) [k /and3P[kl H1 H2]].
  have kp : k < size p.
    rewrite ltnNge; apply/negP => pk.
    move: H2.
    destruct q as [[q Kq] Hq]; simpl in *.
    destruct p as [[p Kp] Hp]; simpl in *.
    rewrite /pad_seqR /= Kq -size_qp Kq 2!nth_cat size_qp (ltnNge k) pk /= nth_nseq.
    by case: ifPn.
  rewrite in_setU; apply/orP; right; rewrite !inE size_qp eqxx /=.
  apply/existsP; exists (Ordinal kp) => /=.
  destruct q as [[q Kq] Hq]; simpl in *.
  destruct p as [[p Kp] Hp]; simpl in *.
  move: H1 H2.
  rewrite /pad_seqR /= Kq -size_qp Kq 2!take_cat size_qp kp => /eqP ->.
  by rewrite eqxx /= nth_cat size_qp kp nth_cat kp.
rewrite inE => /orP[|].
  case/bigcupP => /= p'.
  rewrite inE => /andP[p'p pp'].
  rewrite in_setU1 => /orP[/eqP ->{q}|].
    by rewrite inE blexE pp'.
  rewrite !inE => /eqP qp'; by rewrite /blex /lexord /= qp' pp'.
rewrite !inE => /andP[/eqP qp /existsP[k /andP[/eqP H1 H2]]].
rewrite /blex /lexord /= qp /= eqxx; apply/orP; right.
rewrite /lex_bseq lexP ?size_pad_bseqR //.
exists k; apply/and3P; split.
- by rewrite (@leq_trans (size p)) // size_bseq.
- destruct q as [[q Kq] Hq]; simpl in *.
  destruct p as [[p Kp] Hp]; simpl in *.
  apply/eqP.
  by rewrite /pad_seqR /= Kq -[in if _ then _ else _]qp Kq 2!take_cat qp !(ltn_ord k).
- destruct q as [[q Kq] Hq]; simpl in *.
  destruct p as [[p Kp] Hp]; simpl in *.
  by rewrite /pad_seqR /= Kq -[in if _ then _ else _]qp Kq 2!nth_cat qp (ltn_ord k).
Qed.

Lemma LOUDSpos_of_posE l (p : l.-pos t) :
  LOUDSpos_of_pos p =
    (\sum_(x in (\bigcup_(q in ancestors p) (q |: generation q)) :|: lgeneration p)
      (children_of_pos x).+1).+2.
Proof. congr (_.+2); apply eq_bigl => x; by rewrite -predsE inE. Qed.

Lemma LOUDSpos_of_pos_incr l (a b : l.-pos t) : blex ord0 a b ->
  LOUDSpos_of_pos a <= LOUDSpos_of_pos b.
Proof.
move=> ab; rewrite /LOUDSpos_of_pos !ltnS.
rewrite [in X in _ <= X](bigID (fun x : l.-pos t => blex ord0 x a)) /=.
rewrite [in X in _ <= X](eq_bigl (fun x : l.-pos t => blex ord0 x a)) ?leq_addr //.
move=> q; apply/idP/idP => [/andP[]//|qa]; by rewrite qa andbT (blex_trans qa).
Qed.

Lemma LOUDSpos_of_positionnil l : LOUDSpos_of_pos (positionnil l t) = 2.
Proof.
rewrite /LOUDSpos_of_pos (eq_bigl (fun=> false)) ?big_pred0 // => p.
by rewrite blex_bseq0.
Qed.

End LOUDS_position.

Section LOUDS_children.

Variable (A : finType) (n : nat) (t : btree A n.+2).

Definition LOUDS_children (v : nat(*counting from 0*)) :=
  succ false (LOUDS t) v.+1 - v.+1. (*NB(rei): no .+1 in navarro because he counts from 1...*)
(*NB(rei): similar def in louds *)

Lemma succ_LOUDSpos_of_pos' l (p : l.-pos t) :
  select false
    (rank false (\sum_(x : l.-pos t| blex ord0 x p) (children_of_pos x).+1)
       (level_order_children_traversal (@node_description A) t)).+1
    (level_order_children_traversal (@node_description A) t) =
  (\sum_(x : l.-pos t| blex ord0 x p) (children_of_pos x).+1).+1 + children_of_pos p.
Proof.
move: l p; apply pos_ind => l p IH.
case/boolP : (p == positionnil _ t) => [/eqP ->|p0].
  rewrite (eq_bigl xpred0) ?big_pred0 //; last by move=> q; rewrite /= blex_bseq0.
  rewrite rank0 add1n.
  admit.
Admitted.

Lemma succ_LOUDSpos_of_pos l (p : l.-pos t) :
  succ false (LOUDS t) (LOUDSpos_of_pos p).+1 = (LOUDSpos_of_pos p).+1 + children_of_pos p.
Proof.
rewrite /succ [_.+1.-1]/= select_cons_neq // select_cons_eq 2!addSn; congr (_.+2).
by rewrite rank_cons add0n rank_cons add1n succ_LOUDSpos_of_pos'.
Qed.

Lemma LOUDS_children_correct l (p : l.-pos t) :
  LOUDS_children (LOUDSpos_of_pos p) = children_of_pos p.
Proof. by rewrite /LOUDS_children succ_LOUDSpos_of_pos addnC addnK. Qed.

End LOUDS_children.
End louds_tentative.
