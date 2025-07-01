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
  pname = "trocq-hott-examples";
  inherit (trocq.hott) version;

  src = cleanSource ../../../examples;

  makeFlags = [
    "-C"
    "hott"
  ];

  propagatedBuildInputs = [
    trocq.hott
  ];
}
