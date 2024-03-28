{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean.url = "github:leanprover/lean4?ref=b4caee80a3dfc5c9619d88b16c40cc3db90da4e2";
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    lean,
    ...
  } : flake-parts.lib.mkFlake { inherit inputs; } {
    flake = {
    };
    systems = [
      "x86_64-linux"
      "x86_64-darwin"
    ];
    perSystem = { system, pkgs, ... }: let
      leanPkgs = lean.packages.${system};
      project = leanPkgs.buildLeanPackage {
        name = "Pantograph";
        roots = [ "Main" "Pantograph" ];
        src = ./.;
      };
      test = leanPkgs.buildLeanPackage {
        name = "Test";
        roots = [ "Main" ];
        src = ./Test;
      };
    in rec {
      packages = {
        inherit (leanPkgs) lean lean-all;
        inherit (project) sharedLib executable;
        default = project.executable;
      };
      checks = {
        test = test.executable;
      };
      devShells.default = project.devShell;
    };
  };
}
