(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
Require Import HoTT_additions Database.
From elpi Require Import elpi.

From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi.generation Extra Dependency "hierarchy.elpi" as hierarchy_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Polymorphic Inductive Cumulativity.

(* Coq representation of the hierarchy *)
Inductive map_class : Set := map0 | map1 | map2a | map2b | map3 | map4.

Register map0 as trocq.indc_map0.
Register map1 as trocq.indc_map1.
Register map2a as trocq.indc_map2a.
Register map2b as trocq.indc_map2b.
Register map3 as trocq.indc_map3.
Register map4 as trocq.indc_map4.

(*************************)
(* Parametricity Classes *)
(*************************)

(* first unilateral witnesses describing one side of the structure given to a relation *)

Module Map0.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {}.
End Map0.

Module Map1.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B
}.
End Map1.

Module Map2a.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b
}.
End Map2a.

Module Map2b.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map2b.

Module Map3.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map3.

Module Map4.
(* An alternative presentation of Sozeau, Tabareau, Tanter's univalent parametricity:
   symmetrical and transport-free *)
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b;
  R_in_mapK : forall (a : A) (b : B) (r : R a b), (map_in_R a b (R_in_map a b r)) = r
}.
End Map4.

Register Map0.Has as trocq.map0.
Register Map1.Has as trocq.map1.
Register Map2a.Has as trocq.map2a.
Register Map2b.Has as trocq.map2b.
Register Map3.Has as trocq.map3.
Register Map4.Has as trocq.map4.

(* syntactic representation of annotated universes
 * useful to annotate the initial goal with fresh variables of type map_class
 * that will be mapped to variables in the constraint graph
 *)
Definition PType@{i} (m n : map_class) (* : Type@{i+1} *) := Type@{i}.
(* placeholder for a weakening from (m, n) to (m', n')
 * replaced with a real weakening function once the ground classes are known
 *)
Definition weaken@{i} (m n m' n' : map_class) {A : Type@{i}} (a : A) : A := a.
Register PType as trocq.ptype.
Register weaken as trocq.weaken.

Definition sym_rel@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := fun b a => R a b.

Register sym_rel as trocq.sym_rel.
Register paths as trocq.paths.

Elpi Command genhierarchy.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util.
Elpi Accumulate File util_rocq.
Elpi Accumulate File class.

Elpi Query lp:{{
  {{:gref lib:trocq.ptype}} = const PType,
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.ptype PType)),
  {{:gref lib:trocq.weaken}} = const Weaken,
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.weaken Weaken)),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.sym-rel {{:gref lib:trocq.sym_rel}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (pi UI\
    trocq.db.paths UI (pglobal {{:gref lib:trocq.paths}} UI)
  )),

  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map0 {{:gref lib:trocq.map0}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map1 {{:gref lib:trocq.map1}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map2a {{:gref lib:trocq.map2a}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map2b {{:gref lib:trocq.map2b}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map3 {{:gref lib:trocq.map3}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map->class map4 {{:gref lib:trocq.map4}})),

  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map0 {{:gref lib:trocq.indc_map0}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map1 {{:gref lib:trocq.indc_map1}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map2a {{:gref lib:trocq.indc_map2a}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map2b {{:gref lib:trocq.indc_map2b}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map3 {{:gref lib:trocq.indc_map3}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.map-class->indc-class map4 {{:gref lib:trocq.indc_map4}})).
}}.

(********************)
(* Record Hierarchy *)
(********************)

Elpi Accumulate File hierarchy_generation.
Elpi Accumulate lp:{{
  main-interp [] _ :-
    std.forall {param-class.all-of-kind all} (Class\ sigma ModuleName\
      param-class.add-suffix Class "Param" ModuleName,
      coq.env.begin-module ModuleName none,
      generate-module Class,
      coq.env.end-module _
    ).
}}.

#[synterp] Elpi Accumulate File util.
#[synterp] Elpi Accumulate File class.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [] _ :-
    std.forall {param-class.all-of-kind all} (Class\ sigma ModuleName\
      param-class.add-suffix Class "Param" ModuleName,
      coq.env.begin-module ModuleName none,

      coq.env.end-module _
    ).
}}.

Elpi genhierarchy.

Print Param01.

(********************)
(* Record Weakening *)
(********************)

Elpi Query lp:{{
  std.forall {map-class.all-of-kind all} m\ sigma SubClasses\
    map-class.weakenings-from m SubClasses,
    std.forall SubClasses m'\ sigma Name GR GR'\
     trocq.db.map->class m GR, trocq.db.map->class m' GR',
     map-class.add-2-suffix "" m m' "forgetMap" Name,
     util.add-named-coe Name GR GR' _.
}}.

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-forget.
}}.

(* General projections *)

Definition rel {A B} (R : Param00.Rel A B) := Param00.R A B R.
Coercion rel : Param00.Rel >-> Funclass.

Definition map {A B} (R : Param10.Rel A B) : A -> B :=
  Map1.map _ (Param10.covariant A B R).
Definition map_in_R {A B} (R : Param2a0.Rel A B) :
  forall (a : A) (b : B), map R a = b -> R a b :=
  Map2a.map_in_R _ (Param2a0.covariant A B R).
Definition R_in_map {A B} (R : Param2b0.Rel A B) :
  forall (a : A) (b : B), R a b -> map R a = b :=
  Map2b.R_in_map _ (Param2b0.covariant A B R).
Definition R_in_mapK {A B} (R : Param40.Rel A B) :
  forall (a : A) (b : B), map_in_R R a b o R_in_map R a b == idmap :=
  Map4.R_in_mapK _ (Param40.covariant A B R).

Definition comap {A B} (R : Param01.Rel A B) : B -> A :=
  Map1.map _ (Param01.contravariant A B R).
Definition comap_in_R {A B} (R : Param02a.Rel A B) :
  forall (b : B) (a : A), comap R b = a -> R a b :=
  Map2a.map_in_R _ (Param02a.contravariant A B R).
Definition R_in_comap {A B} (R : Param02b.Rel A B) :
  forall (b : B) (a : A), R a b -> comap R b = a :=
  Map2b.R_in_map _ (Param02b.contravariant A B R).
Definition R_in_comapK {A B} (R : Param04.Rel A B) :
  forall (b : B) (a : A), comap_in_R R b a o R_in_comap R b a == idmap :=
  Map4.R_in_mapK _ (Param04.contravariant A B R).

(* Aliasing *)

Declare Scope param_scope.
Local Open Scope param_scope.
Delimit Scope param_scope with P.

Notation UParam := Param44.Rel.
Notation MkUParam := Param44.BuildRel.
Notation "A <=> B" := (Param44.Rel A B) : param_scope.
Notation IsUMap := Map4.Has.
Notation MkUMap := Map4.BuildHas.
Arguments Map4.BuildHas {A B R}.
Arguments Param44.BuildRel {A B R}.

(* General theorems *)
Lemma ind_map@{i} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') a
  (P : forall a', AR a a' -> map AR a = a' -> Type@{i}) :
  (P (map AR a) (map_in_R AR a (map AR a) 1%path) 1%path) ->
  forall a' aR, P a' aR (R_in_map AR a a' aR).
Proof.
by move=> P1 a' aR; rewrite -[X in P _ X](R_in_mapK AR); case: _ / R_in_map.
Defined.

Lemma ind_mapP@{i +} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') (a : A)
  (P : forall a', AR a a' -> map@{i} AR a = a' -> Type@{i})
  (P1 : P (map@{i} AR a) (map_in_R@{i} AR a (map@{i} AR a) 1%path) 1%path)
  (Q : forall a' aR e, P a' aR e -> Type@{i}) :
   Q (map@{i} AR a) (map_in_R@{i} AR a (map@{i} AR a) 1%path) 1%path P1 ->
  forall a' aR,
     Q a' aR (R_in_map@{i} AR a a' aR) (@ind_map@{i} A A' AR a P P1 a' aR).
Proof.
rewrite /ind_map => Q1 a' aR.
case: {1 6}_ / R_in_mapK.
by case: _ / R_in_map.
Defined.

Lemma weak_ind_map@{i} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') a
  (P : forall a', AR a a' -> Type@{i}) :
  (P (map AR a) (map_in_R AR a (map AR a) 1%path)) ->
  forall a' aR, P a' aR.
Proof. by move=> P1 a' aR; elim/(ind_map AR): aR / _. Defined.

Lemma ind_comap@{i} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> comap AR a' = a -> Type@{i}) :
  (P (comap AR a') (comap_in_R AR a' (comap AR a') 1%path) 1%path) ->
  forall a aR, P a aR (R_in_comap AR a' a aR).
Proof.
by move=> P1 a aR; rewrite -[X in P _ X](R_in_comapK AR); case: _ / R_in_comap.
Defined.

Lemma ind_comapP@{i +} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> comap AR a' = a -> Type@{i})
  (P1 : P (comap@{i} AR a') (comap_in_R@{i} AR a' (comap@{i} AR a') 1%path) 1%path)
  (Q : forall a aR e, P a aR e -> Type@{i}) :
   Q (comap@{i} AR a') (comap_in_R@{i} AR a' (comap@{i} AR a') 1%path) 1%path P1 ->
  forall a aR,
     Q a aR (R_in_comap@{i} AR a' a aR) (@ind_comap@{i} A A' AR a' P P1 a aR).
Proof.
rewrite /ind_comap => Q1 a aR.
case: {1 6}_ / R_in_comapK.
by case: _ / R_in_comap.
Defined.

Lemma weak_ind_comap@{i} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> Type@{i}) :
  (P (comap AR a') (comap_in_R AR a' (comap AR a') 1%path)) ->
  forall a aR, P a aR. 
Proof. by move=> P1 a aR; elim/(ind_comap AR): aR / _. Defined.

Definition map_ind@{i} {A A' : Type@{i}} {PA : Param40.Rel@{i} A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a' : A'), PA a a' -> Type@{i})  :
   P a' aR -> P (map PA a) (map_in_R PA a (map PA a) idpath).
Proof. by elim/(ind_map PA): _ aR / _. Defined.

Definition comap_ind@{i} {A A' : Type@{i}} {PA : Param04.Rel@{i} A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a : A), PA a a' -> Type@{i})  :
   P a aR -> P (comap PA a') (comap_in_R PA a' (comap PA a') idpath).
Proof. by elim/(ind_comap PA): _ aR / _. Defined.


(* symmetry lemmas for Map *)

Definition eq_Map0@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof.
  move=> RR' []; exists.
Defined.

Definition eq_Map1@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof.
  move=> RR' [m]; exists. exact.
Defined.

Definition eq_Map2a@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof.
  move=> RR' [m mR]; exists m.
  move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
Defined.

Definition eq_Map2b@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof.
  move=> RR' [m Rm]; unshelve eexists m.
  - move=> a' b /(RR' _ _)/Rm; exact.
Defined.

Definition eq_Map3@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof.
  move=> RR' [m mR Rm]; unshelve eexists m.
  - move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
  - move=> a' b /(RR' _ _)/Rm; exact.
Defined.

Definition eq_Map4@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <~> R' a a') ->
  Map4.Has@{i} R' -> Map4.Has@{i} R.
Proof.
move=> RR' [m mR Rm RmK]; unshelve eexists m _ _.
- move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
- move=> a' b /(RR' _ _)/Rm; exact.
- by move=> a' b r /=; rewrite RmK [_^-1%function _]equiv_funK.
Defined.

(* proofs about Param44 *)

Lemma umap_equiv_sigma (A B : Type@{i}) (R : A -> B -> Type@{i}) :
  IsUMap R <~>
    { map : A -> B |
    { mR : forall (a : A) (b : B), map a = b -> R a b |
    { Rm : forall (a : A) (b : B), R a b -> map a = b |
      forall (a : A) (b : B), mR a b o Rm a b == idmap } } }.
Proof. by symmetry; issig. Defined.

Definition issig_contr (A : Type) `{Funext}
  : {x : A & forall y, x = y} <~> Contr A.
Proof. apply equiv_inverse, equiv_istrunc_unfold. Defined.

Lemma umap_equiv_isfun `{Funext} {A B : Type@{i}}
  (R : A -> B -> Type@{i}) : IsUMap R <~> IsFun R.
Proof.
apply (equiv_composeR' (umap_equiv_sigma _ _ R)).
transitivity (forall x : A, {y : B & {r : R x y & forall yr', (y; r) = yr'}});
last first. {
  apply equiv_functor_forall_id => a.
  apply (equiv_compose' (issig_contr _)).
  apply equiv_sigma_assoc'.
}
apply (equiv_compose' (equiv_sig_coind _ _)).
apply equiv_functor_sigma_id => map.
apply (equiv_compose' (equiv_sig_coind _ _)).
apply (equiv_composeR' (equiv_sigma_symm _)).
transitivity {f : forall x, R x (map x) &
  forall (x : A) (y : B) (r :  R x y), (map x; f x) = (y; r)};
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: (equiv_composeR' equiv_forall_sigma).
}
transitivity
  { f : forall x, R x (map x) &
    forall (x : A) (y : B) (r :  R x y), {e : map x = y & e # f x = r} };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  apply (equiv_compose' equiv_path_sigma_dp).
  apply equiv_functor_sigma_id => e.
  reflexivity.
}
transitivity
  { f : forall x, R x (map x) &
    forall x y, {g : forall (r :  R x y), map x = y &
    forall (r :  R x y), g r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  exact: equiv_sig_coind.
}
transitivity  { f : forall x, R x (map x) &
    forall x, { g : forall (y : B) (r :  R x y), map x = y &
                forall (y : B) (r :  R x y), g y r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: equiv_sig_coind.
}
transitivity
  { f : forall x, R x (map x) &
    {g : forall (x : A) (y : B) (r :  R x y), map x = y &
         forall x y r, g x y r # f x = r } };
last first.
{ apply equiv_functor_sigma_id => comap; exact: equiv_sig_coind. }
apply (equiv_compose' (equiv_sigma_symm _)).
apply equiv_functor_sigma_id => Rm.
transitivity
  { g : forall (x : A) (y : B) (e : map x = y), R x y &
    forall (x : A) (y : B) (r : R x y), Rm x y r # g x (map x) idpath = r }. {
  apply equiv_functor_sigma_id => mR.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  all: move=> r'; elim r'; elim (Rm a b r); reflexivity.
}
symmetry.
unshelve eapply equiv_functor_sigma.
- move=> mR a b e; exact (e # mR a).
- move=> mR mRK x y r; apply: mRK.
- apply: isequiv_biinv.
  split; (unshelve eexists; first by move=> + a; apply) => //.
  move=> r; apply path_forall => a; apply path_forall => b.
  by apply path_arrow; elim.
- by move=> mR; unshelve econstructor.
Defined.

Lemma uparam_equiv `{Univalence} {A B : Type} : (A <=> B) <~> (A <~> B).
Proof.
apply (equiv_compose' equiv_sig_relequiv^-1).
unshelve eapply equiv_adjointify.
- move=> [R mR msR]; exists R; exact: umap_equiv_isfun.
- move=> [R mR msR]; exists R; exact: (umap_equiv_isfun _)^-1%equiv.
- by move=> [R mR msR]; rewrite !equiv_invK.
- by move=> [R mR msR]; rewrite !equiv_funK.
Defined.

Definition id_umap {A : Type} : IsUMap (@paths A) :=
  MkUMap idmap (fun a b r => r) (fun a b r => r) (fun a b r => 1%path).

Definition id_sym_umap {A : Type} : IsUMap (sym_rel (@paths A)) :=
  MkUMap idmap (fun a b r => r^) (fun a b r => r^) (fun a b r => inv_V r).

Definition id_uparam {A : Type} : A <=> A :=
  MkUParam id_umap id_sym_umap.

Lemma uparam_induction `{Univalence} A (P : forall B, A <=> B -> Type) :
  P A id_uparam -> forall B f, P B f.
Proof.
move=> PA1 B f; rewrite -[f]/(B; f).2 -[B]/(B; f).1.
suff : (A; id_uparam) = (B; f). { elim. done. }
apply: path_ishprop; apply: hprop_inhabited_contr => _.
apply: (contr_equiv' {x : _ & A = x}).
apply: equiv_functor_sigma_id => {f} B.
symmetry; apply: equiv_compose' uparam_equiv.
exact: equiv_path_universe.
Defined.

Lemma uparam_equiv_id `{Univalence} A :
  uparam_equiv (@id_uparam A) = equiv_idmap.
Proof. exact: path_equiv. Defined.

(* instances of MapN for A = A *)
(* allows to build id_ParamMN : forall A, ParamMN.Rel A A *)

Definition id_Map0 {A : Type} : Map0.Has (@paths A).
Proof. constructor. Defined.

Definition id_Map0_sym {A : Type} : Map0.Has (sym_rel (@paths A)).
Proof. constructor. Defined.

Definition id_Map1 {A : Type} : Map1.Has (@paths A).
Proof. constructor. exact idmap. Defined.

Definition id_Map1_sym {A : Type} : Map1.Has (sym_rel (@paths A)).
Proof. constructor. exact idmap. Defined.

Definition id_Map2a {A : Type} : Map2a.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition id_Map2a_sym {A : Type} : Map2a.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition id_Map2b {A : Type} : Map2b.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition id_Map2b_sym {A : Type} : Map2b.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition id_Map3 {A : Type} : Map3.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
Defined.

Definition id_Map3_sym {A : Type} : Map3.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
Defined.

Definition id_Map4 {A : Type} : Map4.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
  - exact (fun a b e => 1%path).
Defined.

Definition id_Map4_sym {A : Type} : Map4.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
  - exact (fun A B e => inv_V e).
Defined.

(* generate id_ParamMN : forall A, ParamMN.Rel A A for all M N *)

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-class.all-of-kind all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-id-param (pc m n) U L
    )
  ).
}}.

(* symmetry property for Param *)

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  map-class.all-of-kind all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-param-sym (pc m n) U L
    )
  ).
}}.

Arguments map : simpl never.
Arguments map_in_R : simpl never.
Arguments R_in_map : simpl never.
Arguments R_in_mapK : simpl never.
Arguments comap : simpl never.
Arguments comap_in_R : simpl never.
Arguments R_in_comap : simpl never.
Arguments R_in_comapK : simpl never.
