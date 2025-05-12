{
  format = "1.0.0";

  shell-attribute = "devshell";
  attribute = "trocq";

  default-bundle = "coq-9.0";
  bundles."coq-8.20" = {
    trocq-std.main-job = true;
    trocq-hott.main-job = true;

    coqPackages.coq.override.version = "8.20";
    coqPackages.coq-elpi.override.version = "master";
  };
  bundles."coq-9.0" = {
    trocq-std.main-job = true;
    trocq-hott.main-job = true;

    coqPackages.coq.override.version = "9.0";
    coqPackages.coq-elpi.override.version = "master";
    rocqPackages.rocq-elpi.override.version = "master";
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
