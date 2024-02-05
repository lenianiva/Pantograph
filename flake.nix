{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean.url = "github:leanprover/lean4?ref=v4.1.0";
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
    in rec {
      packages = project // {
        inherit (leanPkgs) lean;
        lake = leanPkgs.Lake-Main.executable;
        default = packages.executable;
      };
      devShells.default = project.devShell;
    };
  };
}
