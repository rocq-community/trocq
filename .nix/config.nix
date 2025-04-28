{
  format = "1.0.0";

  attribute = "trocq";

  default-bundle = "8.20";
  bundles."8.20" = {
    coqPackages.coq.override.version = "8.20";
    coqPackages.mathcomp.override.version = "master";
    coqPackages.mathcomp-algebra.override.version = "master";
    coqPackages.mathcomp-ssreflect.override.version = "master";
    coqPackages.mathcomp-fingroup.override.version = "master";
    coqPackages.hierarchy-builder.override.version = "master";
    coqPackages.coq-elpi.override.version = "master";
    coqPackages.coq-elpi.override.elpi-version = "2.0.7";
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
