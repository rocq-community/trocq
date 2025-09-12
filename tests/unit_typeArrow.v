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

From Trocq Require Import Trocq.

Set Universe Polymorphism.

Section TypeArrow.
    Variable (L : Type -> Type) (L' : Type -> Type).
    Variable (f : forall (A : Type) (A' : Type), (A' -> A) -> L' A -> L A').

    Definition RL (A : Type) (A' : Type) (AR : Param01.Rel A A')
        := mkParam01 (f A A' (Map1.map _ (Param01.contravariant _ _ AR))).
    Trocq Logging trace.
    Trocq Use RL.

    Goal (forall A : Type, L A).
        trocq.
        enough (x : (fun A : Type, L' A)) by exact x.
    Abort.

End TypeArrow.