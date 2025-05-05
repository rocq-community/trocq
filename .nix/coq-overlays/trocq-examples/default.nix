{
  stdenv,
  lib,
  trocq,
  trocq-std-examples,
}:

stdenv.mkDerivation rec {
  name = "trocq-examples";
  inherit (trocq) version;

  dontUnpack = true;

  passthru = {
    std = trocq-std-examples;
  };

  propagatedBuildInputs = lib.attrValues passthru;
}
