{
  lib,
  mkCoqDerivation,
  coq-elpi,
  trocq,
}:

mkCoqDerivation {
  pname = "trocq-std";
  inherit (trocq) version;

  buildFlags = [ "std" ];

  checkTarget = [ "test-std" ];

  installTargets = [ "install-std" ];

  propagatedBuildInputs = [
    coq-elpi
  ];
}
