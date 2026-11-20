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
From Trocq Require Import Trocq.
From Trocq.Elpi Extra Dependency "fake-aterm.elpi" as fake_aterm.

Axiom P : nat -> Type.

Elpi Command Test.
Elpi Accumulate File fake_aterm.
Elpi Accumulate Db trocq.db.
Elpi Accumulate lp:{{

pred test-fake-map-class->map-class.
test-fake-map-class->map-class :- std.do! [
    fake-map-class->map-class {{ map0 }} map0,
    fake-map-class->map-class {{ map1 }} map1,
    fake-map-class->map-class {{ map2a }} map2a,
    fake-map-class->map-class {{ map2b }} map2b,
    fake-map-class->map-class {{ map3 }} map3,
    fake-map-class->map-class {{ map4 }} map4,
    % it does not support evars.
    do-not-fail => not(fake-map-class->map-class {{ _ }} _)
].

pred test-map-class->fake-map-class.
test-map-class->fake-map-class :- std.do! [
    map-class->fake-map-class map0 {{ map0 }},
    map-class->fake-map-class map1 {{ map1 }},
    map-class->fake-map-class map2a {{ map2a }},
    map-class->fake-map-class map2b {{ map2b }},
    map-class->fake-map-class map3 {{ map3 }},
    map-class->fake-map-class map4 {{ map4 }},

    % it supports uvars!
    map-class->fake-map-class Uvar Evar,
    var Evar,
    % but if the uvar is assigned, the evar should be resolved.
    Uvar = map0, not (var Evar), Evar = {{ map0 }}
].

pred test-fake-aterm->aterm.
test-fake-aterm->aterm :- std.do! [
    coq.locate "nat" Nat,

    % Sorts. Either the param-class of the sort is exactly specified via `PType`, or not if `Type` is used. In this case, the param-class is a unification variable.
    fake-aterm->aterm {{ PType map3 map1 }} (asort (typ _) (pc map3 map1)),
    fake-aterm->aterm {{ Type }} (asort (typ _) PC), var PC,

    % Triples (N, N', NR).
    % Such a triple can be given exactly using `PTriple N N' NR`.
    % In fake aterms, a global constant G is translated to a triple (G, G', GR) where G' and GR are unification variable. However, currently, triples of grefs are represented via aglobal instead of atriple.
    fake-aterm->aterm {{ nat }} (aglobal Nat Nat' Rnat), var Nat', var Rnat,
    fake-aterm->aterm {{ PTriple nat bool (fun _ _ => True) }} (aglobal Nat {{ bool }} {{ fun _ _ => True }}),
    fake-aterm->aterm {{ PTriple (fun x: nat => x) (fun x: nat => x) (fun _ _ => True) }} (
        atriple {{ fun x: nat => x }} {{ fun x: nat => x }} {{ fun _ _ => True }}
    ),

    % Lambda abstractions, foralls and applications.
    fake-aterm->aterm {{ fun (n: nat) => P n }} (afun _ {fake-aterm->aterm {{ nat }}} (n\ 
        aapp [{fake-aterm->aterm {{ P }}}, n]
    )),
    fake-aterm->aterm {{ forall (n: nat), P n }} (aprod _ {fake-aterm->aterm {{ nat }}} (n\ 
        aapp [{fake-aterm->aterm {{ P }}}, n]
    )),

    % Constructions not supported cause an error
    do-not-fail => not (fake-aterm->aterm {{ _ }} _)
].

pred test-aterm->fake-aterm.
test-aterm->fake-aterm :- std.do! [
    coq.locate "nat" Nat,
    Id = {{ fun x: nat => x }},
    FullRel = {{ fun _ _ => True }},

    % Triples
    aterm->fake-aterm (atriple Id Id FullRel) {{ PTriple lp:Id lp:Id lp:FullRel }},
    aterm->fake-aterm (aglobal Nat {{ nat }} FullRel) {{ PTriple nat nat lp:FullRel }},

    % Sorts
    aterm->fake-aterm (asort (typ _) (pc map4 map3)) {{ PType map4 map3 }},

    % Lambda abstractions, foralls and applications.
    aterm->fake-aterm (afun `n` {fake-aterm->aterm {{ nat }}} (n\ 
        aapp [{fake-aterm->aterm {{ P }}}, n]
    )) {{ fun (n: PTriple nat _ _) => (PTriple P _ _) n }},
    aterm->fake-aterm (aprod `n` {fake-aterm->aterm {{ nat }}} (n\ 
        aapp [{fake-aterm->aterm {{ P }}}, n]
    )) {{ forall (n: PTriple nat _ _), (PTriple P _ _) n }},

    % Uvars are supported too.
    aterm->fake-aterm Uvar T,
    var T,
    % and if the uvar is assigned, the evar should be assigned too.
    Uvar = (asort (typ _) (pc map4 map3)),
    not (var T),
    T = {{ PType map4 map3 }}
].

main _ :-
    test-fake-map-class->map-class,
    test-map-class->fake-map-class,
    test-fake-aterm->aterm,
    test-aterm->fake-aterm.

}}.

Elpi Test.