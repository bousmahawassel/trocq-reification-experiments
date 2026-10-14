{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs, ... }:
  let
    # Helper functions
    forAllSystems = nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed;
  in
  {
    devShells = forAllSystems (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        default = pkgs.callPackage ./nix/shell.nix { trocq = self.packages.${system}.trocq; patat = self.packages.${system}.patat; coqutil = self.packages.${system}.coqutil; };
	withEmacs = pkgs.callPackage ./nix/shell.nix { withEmacs = true; trocq = self.packages.${system}.trocq; patat = self.packages.${system}.patat; coqutil = self.packages.${system}.coqutil; };
      }
    );

    packages = forAllSystems (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      rec {
        default = pkgs.callPackage ./nix/package.nix {
          trocq = trocq;
	  patat = patat;
	  coqutil = coqutil;
        };
        trocq = pkgs.callPackage ./nix/trocq.nix { };
        patat = pkgs.callPackage ./nix/patat.nix { };
        coqutil = pkgs.callPackage ./nix/coqutil.nix { };
      }
    );
  };
}

