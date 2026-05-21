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

From Trocq Require Import Stdlib Trocq.

Set Universe Polymorphism.

Section TrocqCoercionOnOff.

    Variable (A B: Type).
    Variable (f : B -> A).

    Definition R1 : Param10.Rel B A := mkParam10 f.

    Trocq DB Register R1.

    Trocq Use R1 : R1.
    Goal A.
        Fail (enough (x : B) by exact x).
    Abort.

    Trocq Coercion On with R1.
    Goal A.
        enough (x : B) by exact x.
    Abort.

    Trocq Coercion Off.
    Goal A.
        Fail (enough (x : B) by exact x).
    Abort.
End TrocqCoercionOnOff.
