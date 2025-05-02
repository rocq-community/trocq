{
  lib,
  mkCoqDerivation,
  coq,
  coq-elpi,
  version ? null,
}:

mkCoqDerivation {
  pname = "trocq";
  inherit version;

  makeFlags = [ "-C" "std" ];

  propagatedBuildInputs = [
    coq-elpi
  ];
}
