{
  lib,
  mathcomp,
  mkCoqDerivation,
  version ? null,
  trocq,
}:

with lib;
mkCoqDerivation {
  pname = "trocq-hott-examples";
  inherit (trocq.hott) version;

  src = ../../../examples;

  propagatedBuildInputs = [
    trocq.hott
    mathcomp.ssreflect
    mathcomp.algebra
  ];
}
