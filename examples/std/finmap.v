From mathcomp Require Import all_boot finmap.
From Trocq Require Import Stdlib Trocq.
Require Import gmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Instance countable_dec_eq (K : countType) : base.RelDecision (@eq K).
Proof.
Admitted.

Instance countable_countable (K : countType) : countable.Countable K.
Proof.
unshelve esplit.
- move=> k.
  exact (BinPos.Pos.of_nat (choice.pickle k).+1).
- move=> /BinPos.Pos.to_nat/predn.
  exact choice.unpickle.
move=> k /=.
by rewrite Pnat.Nat2Pos.id// choice.pickleK.
Defined.

Definition gset_insert T `{base.RelDecision _ _ (@eq T)} `{countable.Countable T} (X : gset T) (x : T) :=
  gset_union X (gset_singleton x).

Definition gset_of_seq T `{base.RelDecision _ _ (@eq T)} `{countable.Countable T} (s : seq T) :=
  foldl gset_insert gset_empty s.

Lemma elem_of_gset_insert T `{base.RelDecision _ _ (@eq T)} `{countable.Countable T} (X : gset T) (x y : T) :
  base.elem_of y (gset_insert X x) <-> x = y \/ base.elem_of y X.
Proof.
rewrite base.elem_of_union base.or_comm.
apply: ZifyClasses.or_morph => //.
rewrite -[gset_singleton x]/(base.singleton _).
rewrite base.elem_of_singleton.
by split.
Qed.

Lemma elem_of_gset_of_seq T `{base.RelDecision _ _ (@eq T)} `{countable.Countable T} (s : seq T) (x : T) :
  base.elem_of x (gset_of_seq s) <-> base.elem_of x s.
Proof.
admit.
(*rewrite -list_basics.list.elem_of_reverse.
Search list_basics.list.reverse rev.
  Search base.elem_of seq.
elim: s => [|y s IHs].
  by rewrite sets.elem_of_empty list_basics.list.elem_of_nil.
  Search foldl foldr.
  rewrite /gset_of_seq/=.
   rewrite -[gset_of_seq _]/(base.union _ _) base.elem_of_union./*)
  Admitted.

Lemma mem_elem_ofE (T : eqType) (s : seq T) (x : T) :
  (x \in s : Prop) <-> base.elem_of x s.
Proof.
elim: s => [|y s IHs].
  by rewrite in_nil list_basics.list.elem_of_nil; split.
rewrite in_cons list_basics.list.elem_of_cons -IHs.
rewrite [X in X <-> _]Bool.orb_true_iff.
by apply: or_iff_compat_r; split=> /eqP.
Qed.

Lemma Param42a_gset_fset_d_subproof (K : countType) (X : {fset K}) :
  seq_fset tt (base.elements (gset_of_seq (enum_fset X))) = X.
Proof.
apply/fsetP => x.
rewrite seq_fsetE.
apply: Bool.eq_true_iff_eq.
rewrite -[_ = true]/(_ \in _ : Prop).
rewrite mem_elem_ofE base.elem_of_elements.
by rewrite elem_of_gset_of_seq -mem_elem_ofE.
Qed.

(* gset ~ fset *)
Definition Param42a_gset_fset_d (K : countType) : Param42a.Rel (gset K) {fset K}.
Proof.
apply: SplitSurj.toParam.
unshelve eexists.
- move=> X; exact (seq_fset tt (base.elements X)).
- move=> X; exact: (gset_of_seq (enum_fset X)).
- exact: Param42a_gset_fset_d_subproof.
Defined.

Definition gset_fsetR {K : countType} := rel (Param42a_gset_fset_d K).

(* gset_empty ~ fset0 *)

Definition Param_gset_empty_fset0_d {K : countType} : gset_fsetR (@gset_empty K _ _) (@fset0 K).
Proof. by apply/fsetP => x; rewrite in_fset0 seq_fsetE. Defined.

Definition Param_gset_singleton_fset1_d {K : countType} (x : K) :
  gset_fsetR (gset_singleton x) (fset1 x).
Proof.
apply/fsetP => y; rewrite in_fset1 seq_fsetE.
apply: Bool.eq_true_iff_eq.
rewrite -[_ = true]/(_ \in _ : Prop) mem_elem_ofE base.elem_of_elements.
rewrite -[gset_singleton _]/(base.singleton _) base.elem_of_singleton.
by split=> /eqP.
Defined.

Definition Param_gset_union_fsetU_d {K : countType}
    {X1 : gset K} {Y1 : {fset K}} (R1 : gset_fsetR X1 Y1)
    {X2 : gset K} {Y2 : {fset K}} (R2 : gset_fsetR X2 Y2) :
  gset_fsetR (gset_union X1 X2) (fsetU Y1 Y2).
Proof.
apply/fsetP => x; rewrite in_fsetU -R1 -R2 !seq_fsetE.
apply: Bool.eq_true_iff_eq.
rewrite -[_ = true]/(_ \in _ : Prop).
rewrite Bool.orb_true_iff -![_ = true]/(_ \in _ : Prop).
by rewrite !mem_elem_ofE !base.elem_of_elements base.elem_of_union.
Defined.

Definition Param_gset_intersection_fsetI_d {K : countType}
    {X1 : gset K} {Y1 : {fset K}} (R1 : gset_fsetR X1 Y1)
    {X2 : gset K} {Y2 : {fset K}} (R2 : gset_fsetR X2 Y2) :
  gset_fsetR (gset_intersection X1 X2) (fsetI Y1 Y2).
Proof.
apply/fsetP => x; rewrite in_fsetI -R1 -R2 !seq_fsetE.
apply: Bool.eq_true_iff_eq.
rewrite -[_ = true]/(_ \in _ : Prop).
rewrite Bool.andb_true_iff -![_ = true]/(_ \in _ : Prop).
by rewrite !mem_elem_ofE !base.elem_of_elements base.elem_of_intersection.
Defined.

Definition Param_gset_difference_fsetD_d {K : countType}
    {X1 : gset K} {Y1 : {fset K}} (R1 : gset_fsetR X1 Y1)
    {X2 : gset K} {Y2 : {fset K}} (R2 : gset_fsetR X2 Y2) :
  gset_fsetR (gset_difference X1 X2) (fsetD Y1 Y2).
Proof.
apply/fsetP => x; rewrite in_fsetD -R1 -R2 !seq_fsetE andbC.
apply: Bool.eq_true_iff_eq.
rewrite -[_ = true]/(_ \in _ : Prop).
rewrite Bool.andb_true_iff -[_ = true]/(_ \in _ : Prop).
have notP (b : bool) : ~ b <-> ~~ b by split=> /negP.
rewrite -[_ = true]notP.
by rewrite !mem_elem_ofE !base.elem_of_elements base.elem_of_difference.
Defined.

Trocq Use RTrue Runit.


  
  
