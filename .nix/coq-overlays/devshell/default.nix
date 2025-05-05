{
  mkCoqDerivation,
  lib,
  trocq,
  ...
}:

mkCoqDerivation {
  pname = "devshell";
  inherit (trocq) version;

  errorPhase = ''
    echo
    echo '`nix-build` is not supported.'
    echo
    echo 'You can either:'
    echo '- run ${
      lib.concatMapStringsSep " or " (variant: "`nix-build --argstr job ${variant.pname}`") trocq.variants
    }'
    echo '- if you want to experiment, run `nix-shell` to spawn a shell with the dependencies of all trocq variants.'
    echo '  You can then run `make`, ${
      lib.concatMapStringsSep " or " (
        variant: "`make ${lib.removePrefix "trocq-" variant.pname}`"
      ) trocq.variants
    }.'
    echo
    exit
  '';
  prePhases = [ "errorPhase" ];

  buildInputs =
    let
      flattenMap = f: v: lib.flatten (lib.map f v);
    in
    lib.unique (
      flattenMap (attr: flattenMap (v: v.${attr}) trocq.variants) [
        "propagatedBuildInputs"
        "buildInputs"
        "propagatedNativeBuildInputs"
        "nativeBuildInputs"
      ]
    );
}
