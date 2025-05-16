{
  mkCoqDerivation,
  lib,
  trocq,
  ...
}:

mkCoqDerivation {
  pname = "devshell";
  inherit (trocq) version;

  src = ../../../.;

  installPhase = ''
    touch $out
  '';

  buildInputs =
    let
      flattenMap = f: v: lib.flatten (lib.map f v);
    in
    lib.unique (
      flattenMap (attr: flattenMap (v: v.${attr}) trocq.variants) [
        "propagatedBuildInputs"
        "buildInputs"
        "propagatedNativeBuildInputs"
        "nativeBuildInputs"
      ]
    );
}
