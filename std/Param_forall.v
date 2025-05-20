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

From elpi Require Import elpi.
Require Import ssreflect.
Require Import Stdlib Hierarchy Database Param_lemmas.

From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.
From Trocq.Elpi.generation Extra Dependency "param-forall.elpi" as param_forall_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Import HoTTNotations.
Local Open Scope param_scope.

Elpi Command genparamforall.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util_rocq.
Elpi Accumulate File param_class_util.

  
Definition R_forall@{i j}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param00.Rel@{j} (B a) (B' a')) :=
    fun f f' => forall a a' aR, (PB a a' aR) (f a) (f' a').

(* MapN for forall *)

(* (00, 00) -> 00 *)
Definition Map0_forall@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param00.Rel@{j} (B a) (B' a')) :
    Map0.Has@{k} (R_forall@{i j} PA PB).
Proof. constructor. Defined.

(* (02a, 10) -> 1 *)
Definition Map1_forall@{i j k}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param10.Rel@{j} (B a) (B' a')) :
    Map1.Has@{k} (R_forall@{i j} PA PB).
Proof.
  constructor.
  exact (fun f a' => map (PB _ _ (comap_in_R _ _ _ 1)) (f (comap PA a'))).
Defined.

(* (04, 2a0) -> 2a0 *)
Definition Map2a_forall@{i j k}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param2a0.Rel@{j} (B a) (B' a')) :
    Map2a.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall@{i j k} PA PB)).
  move=> f f' /= e a a' aR; apply (map_in_R@{j} (PB _ _ _)).
  elim/(ind_comap PA): _ aR / _.
  exact: (ap (fun f => f a') e).
Defined.

(* (02a, 2b0) + funext -> 2b0 *)
Definition Map2b_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param2b0.Rel@{j} (B a) (B' a')) :
    Map2b.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall PA PB)).
  - move=> f f' fR; apply path_forall => a'.
    apply (R_in_map (PB _ _ _)); exact: fR.
Defined.

(* (04, 30) + funext -> 30 *)
Definition Map3_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param30.Rel@{j} (B a) (B' a')) :
    Map3.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall PA PB)).
  - exact: (Map2a.map_in_R _ (Map2a_forall PA PB)).
  - move=> f f' fR; apply path_forall => a'.
    apply (R_in_map (PB _ _ _)); exact: fR.
Defined.

Lemma ap_path_forall `{Funext} X Y (f g : forall x : X, Y x) x (e : f == g):
  ap (fun f => f x) (path_forall f g e) = e x.
Proof. by rewrite -{2}(apD10_retr _ _ e). Qed.

(* (04, 40) + funext -> 40 *)
Definition Map4_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param40.Rel@{j} (B a) (B' a')) :
    Map4.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists
    (Map1.map@{k} _ (Map1_forall PA PB))
    (Map3.map_in_R _ (Map3_forall PA PB))
    (Map3.R_in_map _ (Map3_forall PA PB)).
  move=> f f' fR /=.
  apply path_forall@{i k} => a.
  apply path_forall@{i k} => a'.
  apply path_forall => aR.
  elim/(ind_comapP PA): _ => {a aR}.
  rewrite ap_path_forall.
  by elim/(ind_map (PB (comap PA a') a' (comap_in_R PA a' (comap PA a') 1))): _ _ / _.
 Qed.
(* Param_forallMN : forall A A' AR B B' BR,
     ParamMN.Rel (forall a, B a) (forall a', B' a') *)

Elpi Accumulate File param_forall_generation.
Elpi Query lp:{{
  coq.univ.new Ui,
  coq.univ.variable Ui Li,
  coq.univ.new Uj,
  coq.univ.variable Uj Lj,
  coq.univ.alg-max Ui Uj Uk,
  % cannot have only 2 binders in the declaration because this line creates a fresh level:
  coq.univ.variable Uk Lk,
  map-class.all-of-kind all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-param-forall (pc m n) Ui Uj Li Lj Lk
    )
  ).
}}.
