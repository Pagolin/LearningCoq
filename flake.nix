{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, ... }: flake-utils.lib.eachDefaultSystem (system: let
    pkgs = nixpkgs.legacyPackages.${system};
  in {
    devShells.default = pkgs.mkShellNoCC {
      shellHook = ''
        alias ll="ls -lasi"
        alias spacemacs="HOME=$(pwd) emacs"
      '';
      buildInputs = [
       # (with pkgs.coqPackages_8_18; [coq mathcomp])
        pkgs.coqPackages_8_18.coq
      ];
    };
  }) // {
    templates = {
      coq = {
        description = "Coq development environment and package framework";
        path = ./code/nix/coq;
        welcomeText = ''
          # Simple Coq project template using Dune
          ## Usage
          In `flake.nix`, adapt the `package-name` and `coq-versions` variables
          at the top of the file.  The first entry in `coq-versions` determines
          your default build and development environment.

          The `default.nix` file contains the package build script, which is
          prepared to use Dune for building.  There is documentation in the file
          to guide you how to add dependencies to your package.

          ## Adding to an existing project
          When working in an existing Git project, you need to add the
          `flake.nix`, `flake.lock` and `default.nix` files to git or nix will
          return errors.  `flake.lock` will appear after the first run of `nix
          flake show`.

          ## Entering the development environment
          Enter the default development environment by running `nix develop`.
          Use `nix flake show` to list all known attributes and pick a suitable
          attribute from `devShells` to enter a development environment for a
          different Coq Version.  Enter the development with `nix develop
          .#coqVER-PKG`.
        ''; };

      default = self.templates.coq;
    };
  };
}
