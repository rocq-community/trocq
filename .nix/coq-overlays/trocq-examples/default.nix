{
  lib,
  mathcomp,
  mkCoqDerivation,
  trocq,
}:

with lib;
mkCoqDerivation {
  pname = "trocq-example";
  inherit (trocq) version;

  src = ../../../examples;

  propagatedBuildInputs = [
    trocq
    mathcomp.ssreflect
    mathcomp.algebra
  ];
}
