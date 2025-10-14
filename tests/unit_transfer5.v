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

Section Transfer.

    Variable (I I' : Type) (f : I' -> I) (f' : I -> I').

    Definition Rf' := mkParam30 f'.
    Trocq Use Rf'.

    Variable (pe : I -> Prop) (pe' : I'  -> Prop).
    Definition Rpe
        (n : I) (n' : I') (rn : (Rf') n n')
        : Param01.Rel (pe n) (pe' n').
        admit.
    Admitted.
    Trocq Use Rpe.

    Variable (qe : I -> I -> Prop) (qe' : I' -> I' -> Prop).
    Definition Rqe
        (n : I) (n' : I') (rn : (Rf') n n')
        (m : I) (m' : I') (rm : (Rf') m m')
        : Param10.Rel (qe n m) (qe' n' m').
        admit.
    Admitted.
    Trocq Use Rqe.

    Goal forall (m : I), qe m m -> pe m.
        assert (H : True) by trivial.
        trocq.
        enough (x : forall m : I', qe' m m -> pe' m) by exact x.
    Abort.

End Transfer.
