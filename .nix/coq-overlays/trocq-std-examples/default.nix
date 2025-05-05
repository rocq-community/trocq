{
  lib,
  mathcomp,
  mkCoqDerivation,
  version ? null,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-std-examples";
  inherit (trocq.std) version;

  src = ../../../examples;

  propagatedBuildInputs = [
    trocq.std
    mathcomp.ssreflect
    mathcomp.algebra
  ];
}
