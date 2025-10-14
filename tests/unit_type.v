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

Section TypeTest.

    Variable (A B U : Type).
    Variable (f : A -> B).

    Definition R1 : Param10.Rel A B := mkParam10 f.

    Trocq Use R1.

    Goal A -> Type.
        trocq.
        enough (x : B -> Type) by exact x.
    Abort.

    Goal (fun X : Type => X) (A -> Type).
        trocq.
        enough (x : (fun X : Type => X) (B -> Type)) by exact x.
    Abort.
    

End TypeTest.
