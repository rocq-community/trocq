{
  format = "1.0.0";

  attribute = "trocq";

  no-rocq-yet = true;

  default-bundle = "rocq-9.1";

  bundles = let
    common-bundles = {
      coq-elpi.job = true;
      trocq-std.main-job = true;
      trocq-hott.main-job = true;
    };
  in {
    "coq-8.20".coqPackages = common-bundles // {
      coq.override.version = "8.20";
    };
    "rocq-9.0" = { rocqPackages = {
      rocq-core.override.version = "9.0";
    }; coqPackages = common-bundles // {
      coq.override.version = "9.0";
    }; };
    "rocq-9.1" = { rocqPackages = {
      rocq-core.override.version = "9.1";
    }; coqPackages = common-bundles // {
      coq.override.version = "9.1";
      trocq-hott.job = false;  # HoTT isn't available yet for 9.1
      trocq.job = false;  # depends on trocq-hott
    }; };
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
