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
  });
}
