{
  stdenv,
  lib,
  version ? null,
  trocq-std,
  trocq-hott,
  trocq-std-examples,
  trocq-hott-examples,
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
    examples = [
      trocq-std-examples
      trocq-hott-examples
    ];
  };

  propagatedBuildInputs = passthru.variants;
}
