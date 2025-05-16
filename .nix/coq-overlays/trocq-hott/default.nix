{
  lib,
  mkCoqDerivation,
  coq-elpi,
  HoTT,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-hott";
  inherit (trocq) version;

  makeFlags = [
    "-C"
    "hott"
  ];

  propagatedBuildInputs = [
    coq-elpi
    HoTT
  ];
}
