{
  lib,
  mkCoqDerivation,
  coq,
  coq-elpi,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-std";
  inherit (trocq) version;

  makeFlags = [
    "-C"
    "std"
  ];

  propagatedBuildInputs = [
    coq-elpi
  ];
}
