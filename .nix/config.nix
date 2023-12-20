{
  format = "1.0.0";

  shell-attribute = "devshell";
  attribute = "trocq";

  default-bundle = "coq-9.0";
  bundles."coq-8.20" = {
    coqPackages.trocq-std.main-job = true;
    coqPackages.trocq-hott.main-job = true;

    coqPackages.coq.override.version = "8.20";
  };
  bundles."coq-9.0" = {
    coqPackages.trocq-std.main-job = true;
    coqPackages.trocq-hott.main-job = true;

    coqPackages.coq.override.version = "9.0";
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
