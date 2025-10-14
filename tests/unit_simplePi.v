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

Section SimplePi.
    Variable (A A' : Type) (f : A -> A').
    Variable (B : A -> Type) (B' : A' -> Type).
    Variable (g : forall (X:A) (X':A'), B' X' -> B X).
    Variable (U : Type).

    Definition Rf := mkParam2a0 f.
    Trocq Use Rf.

    Definition Rg (X : A) (X' : A')
        : Param01.Rel (B X) (B' X')
        := mkParam01 (g X X').

    Trocq Use Rg.

    Print Param01_forall.

    (* D(0,1) = ((2a,0),(0,1)) *)
    Goal forall X : A, B X.
        trocq.
        enough (forall X' : A', B' X') by exact x.
    Abort.


End SimplePi.
