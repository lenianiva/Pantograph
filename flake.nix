{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean = {
      url = "github:leanprover/lean4?ref=b4caee80a3dfc5c9619d88b16c40cc3db90da4e2";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    lspec = {
      url = "github:lurk-lab/LSpec?ref=3388be5a1d1390594a74ec469fd54a5d84ff6114";
      flake = false;
    };
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    lean,
    lspec,
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
      lspecLib = leanPkgs.buildLeanPackage {
        name = "LSpec";
        roots = [ "Main" "LSpec" ];
        src = "${lspec}";
      };
      project = leanPkgs.buildLeanPackage {
        name = "Pantograph";
        #roots = pkgs.lib.optional pkgs.stdenv.isDarwin [ "Main" "Pantograph" ];
        roots = [ "Main" "Pantograph" ];
        src = ./.;
      };
      test = leanPkgs.buildLeanPackage {
        name = "Test";
        # NOTE: The src directory must be ./. since that is where the import
        # root begins (e.g. `import Test.Environment` and not `import
        # Environment`) and thats where `lakefile.lean` resides.
        roots = [ "Test.Main" ];
        deps = [ lspecLib project ];
        src = pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            !(pkgs.lib.hasInfix "Pantograph" path);
        };
      };
    in rec {
      packages = {
        inherit (leanPkgs) lean lean-all;
        inherit (project) sharedLib executable;
        test = test.executable;
        default = project.executable;
      };
      checks = {
        test = pkgs.runCommand "test" {
          buildInputs = [ test.executable leanPkgs.lean-all ];
        } ''
          #export LEAN_SRC_PATH="${./.}"
          ${test.executable}/bin/test > $out
        '';
      };
      devShells.default = project.devShell;
    };
  };
}
