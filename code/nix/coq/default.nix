{ package-name }:

# Add all packages here that you want to add to `nativeBuildInputs`,
# `buildInputs` or `propagatedBuildInputs`.
# For OCaml packages, use the coq.ocamlPackages attribute instead.
{
  lib,
  mkCoqDerivation,
  coq,
  doCheck ? false,
}: let
  ignored-paths = [
    "default.nix"
    "flake.nix"
    "flake.lock"
    ".gitignore"
  ];

in mkCoqDerivation rec {

  # Set the package name and version, if needed (defaults to <flake package-name>-0.0.1).
  pname = package-name;
  defaultVersion = "0.0.1";

  useDune = true;

  release.${defaultVersion} = {
    src = lib.const (lib.cleanSourceWith {
      src = lib.cleanSource ./.;
      filter = let
        inherit (lib) all hasSuffix;
        ignorePaths = xs: path: all (x: ! hasSuffix x path) xs;
      in
        path: _: ignorePaths ignored-paths path;
    });
  };

  enableParallelBuilding = true;

  # Add packagse you ONLY need to BUILD (e.g. to produce documentation, compilers
  # etc.).
  nativeBuildInputs = [
  ];

  # Add packages that you need to BUILD AND RUN your program (excl. coq packages).
  buildInputs = [
  ];

  # Add all Coq and OCaml packages here.
  propagatedBuildInputs = with coq.ocamlPackages; [
  ];

  inherit doCheck;
}
