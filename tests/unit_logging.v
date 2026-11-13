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

Section Logging.

    Trocq Logging trace.

    Trocq Logging debug.

    Trocq Logging info.

    Trocq Logging off.

    Variable (A A' : Type).
    Variable (f : A' -> A).
    Definition RA := mkParam01 f.

    Trocq Use RA.

    Trocq Logging trace.
    Goal A.
        trocq.
        enough (x : A') by exact x.
    Abort.

    Trocq Logging off.


End Logging.
