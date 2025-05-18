{
  lib,
  mathcomp,
  mkCoqDerivation,
  version ? null,
  trocq,
}:

let
  cleanSource = source: lib.cleanSourceWith {
    filter = (
      name: type:
      let
        baseName = baseNameOf (toString name);
      in
      type != "regular"
      || !(
        baseName == ".Makefile.d"
        || baseName == "Makefile.conf"
        || lib.hasSuffix ".vo" baseName
        || lib.hasSuffix ".vok" baseName
        || lib.hasSuffix ".vos" baseName
        || lib.hasSuffix ".glob" baseName
        || lib.match "^\..*\.aux$" baseName != null
      )
    );
    src = lib.cleanSource source;
  };
in
mkCoqDerivation {
  pname = "trocq-std-examples";
  inherit (trocq.std) version;

  src = cleanSource ../../../examples;

  makeFlags = [
    "-C"
    "std"
  ];

  propagatedBuildInputs = [
    trocq.std
    mathcomp.ssreflect
    mathcomp.algebra
  ];
}
