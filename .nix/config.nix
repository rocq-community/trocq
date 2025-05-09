{
  format = "1.0.0";

  shell-attribute = "devshell";
  attribute = "trocq";

  default-bundle = "8.20";
  bundles."8.20" = {
    coqPackages.trocq-examples = { };

    coqPackages.coq.override.version = "8.20";
    coqPackages.coq-elpi.override.version = "master";
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
