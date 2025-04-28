rec {
  format = "1.0.0";

  attribute = "trocq";

  default-bundle = "8.20";
  bundles."8.20" = {
    coqPackages.coq.override.version = "8.20";
    coqPackages.coq-elpi.override.version = "master";
    coqPackages.coq-elpi.override.elpi-version = "2.0.7";
  };
  
  bundles."8.20-examples" = {
    coqPackages = bundles."8.20".coqPackages // {
      mathcomp.override.version = "master";
      mathcomp-algebra.override.version = "master";
      mathcomp-ssreflect.override.version = "master";
      mathcomp-fingroup.override.version = "master";
      hierarchy-builder.override.version = "master";
    };
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
