{
  stdenv,
  lib,
  version ? null,
  trocq-std,
  trocq-hott,
  trocq-examples,
}:

stdenv.mkDerivation rec {
  name = "trocq";
  inherit version;

  dontUnpack = true;

  passthru = rec {
    std = trocq-std;
    hott = trocq-hott;

    variants = [
      std
      hott
    ];
    examples = trocq-examples.passthru;
  };

  propagatedBuildInputs = passthru.variants;
}
