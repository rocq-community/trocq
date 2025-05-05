{
  stdenv,
  lib,
  version ? null,
  trocq-std,
  trocq-examples,
}:

stdenv.mkDerivation rec {
  name = "trocq";
  inherit version;

  dontUnpack = true;

  passthru = rec {
    std = trocq-std;

    variants = [
      std
    ];
    examples = trocq-examples.passthru;
  };

  propagatedBuildInputs = passthru.variants;
}
