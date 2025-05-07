{
  stdenv,
  lib,
  trocq,
  trocq-std-examples,
  trocq-hott-examples,
}:

stdenv.mkDerivation rec {
  name = "trocq-examples";
  inherit (trocq) version;

  dontUnpack = true;

  passthru = {
    std = trocq-std-examples;
    hott = trocq-hott-examples;
  };

  propagatedBuildInputs = lib.attrValues passthru;
}
