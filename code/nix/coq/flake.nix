{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
    ...
  }:
    let
      # The name of your program.
      package-name = "program";
      # Coq Versions to use as string, e.g. "8.18" is mapped to
      # `coqPackages8_18`.  First entry determines the default.  Defaults to the
      # current default Coq release.
      coq-versions = [
        (lib.versions.majorMinor nixpkgs.legacyPackages."x86_64-linux".coqPackages.coq.version)
      ];

      inherit (nixpkgs) lib;
    in flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [self.overlays.default];
      };
    in {
      checks = self.lib.genAttrs' coq-versions (v: self.packages.${system}.${self.lib.coqPname v}.override {
        doCheck = true;
      });

      devShells = {
        default = self.lib.firstAttr (v: self.checks.${system}.${self.lib.coqPname v});
      } // (self.lib.genAttrs' coq-versions (v: self.checks.${system}.${self.lib.coqPname v}));

      packages = {
        default = self.lib.firstAttr (v: pkgs.${self.lib.coqAttr v}.${package-name});
      } // (self.lib.genAttrs' coq-versions (v: pkgs.${self.lib.coqAttr v}.${package-name}));
    })
    // {
      lib = {
        coqAttr = ver: "coqPackages_" + (builtins.replaceStrings ["."] ["_"] ver);
        coqPname = ver: "coq" + (builtins.replaceStrings ["."] ["_"] ver) + "-${package-name}";
        firstAttr = f: builtins.head (map (n: f n) coq-versions);
        genAttrs' = names: f: lib.listToAttrs (map (n: lib.nameValuePair (self.lib.coqPname n) (f n)) names);
      };
      overlays.default = final: prev: let
        coqPkg = (import ./default.nix) { inherit package-name; };
        injectPkg = name: set:
          prev.${name}.overrideScope (self: _: {
            ${package-name} = self.callPackage coqPkg {};
          });
      in
        prev.lib.mapAttrs injectPkg (lib.genAttrs (map self.lib.coqAttr coq-versions) (n: final.${n}));
    };
}
