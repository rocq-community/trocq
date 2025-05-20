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

Require Import ssreflect.
Require Import Stdlib Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Import HoTTNotations.
Local Open Scope param_scope.

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

Definition eq_Map0w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof.
  move=> RR' []; exists.
Defined.

Definition eq_Map1w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof.
  move=> RR' [m]; exists. exact.
Defined.

Definition eq_Map2aw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof.
  move=> RR' [m mR]; exists m.
  move=> a' b /mR/(snd (RR' _ _)); exact.
Defined.

Definition eq_Map2bw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof.
  move=> RR' [m Rm]; unshelve eexists m.
  - move=> a' b /(fst (RR' _ _)) /Rm; exact.
Defined.

Definition eq_Map3w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof.
  move=> RR' [m mR Rm]; unshelve eexists m.
  - move=> a' b /mR /(snd (RR' _ _)); exact.
  - move=> a' b /(fst (RR' _ _))/Rm; exact.
Defined.

Definition flipw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
    (forall a a', R a a' <->> R' a a') ->
    (forall a a', R a a' <--> R' a a') :=
fun Rab a a' => ((Rab a a').1, (Rab a a').2.1).

Definition eq_Map0@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof. by move=> /flipw/eq_Map0w. Defined.

Definition eq_Map1@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof. by move=> /flipw/eq_Map1w. Defined.
  
Definition eq_Map2a@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof. by move=> /flipw/eq_Map2aw. Defined.

Definition eq_Map2b@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof. by move=> /flipw/eq_Map2bw. Defined.

Definition eq_Map3@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof. by move=> /flipw/eq_Map3w. Defined.
  
Definition eq_Map4@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map4.Has@{i} R' -> Map4.Has@{i} R.
Proof.
move=> RR' [m mR Rm RmK]; unshelve eexists m _ _.
- move=> a' b /mR /(RR' _ _).2.1; exact.
- move=> a' b /(RR' _ _).1/Rm; exact.
- move=> a' b r /=; rewrite RmK.
  by case: RR' => /= f [/= g ].
Defined.
