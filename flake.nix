{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean = {
      # Do not follow input's nixpkgs since it could cause build failures
      url = "github:leanprover/lean4?ref=v4.12.0";
    };
    lspec = {
      url = "github:argumentcomputer/LSpec?ref=504a8cecf8da601b9466ac727aebb6b511aae4ab";
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
      leanPkgs = lean.packages.${system}.deprecated;
      lspecLib = leanPkgs.buildLeanPackage {
        name = "LSpec";
        roots = [ "Main" "LSpec" ];
        src = "${lspec}";
      };
      project = leanPkgs.buildLeanPackage {
        name = "Pantograph";
        roots = [ "Pantograph" ];
        src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            !(pkgs.lib.hasInfix "/Test/" path) &&
            !(pkgs.lib.hasSuffix ".md" path) &&
            !(pkgs.lib.hasSuffix "Repl.lean" path);
        });
      };
      repl = leanPkgs.buildLeanPackage {
        name = "Repl";
        roots = [ "Main" "Repl" ];
        deps = [ project ];
        src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            !(pkgs.lib.hasInfix "/Test/" path) &&
            !(pkgs.lib.hasSuffix ".md" path);
        });
      };
      test = leanPkgs.buildLeanPackage {
        name = "Test";
        # NOTE: The src directory must be ./. since that is where the import
        # root begins (e.g. `import Test.Environment` and not `import
        # Environment`) and thats where `lakefile.lean` resides.
        roots = [ "Test.Main" ];
        deps = [ lspecLib repl ];
        src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = path: type:
            !(pkgs.lib.hasInfix "Pantograph" path);
        });
      };
    in rec {
      packages = {
        inherit (leanPkgs) lean lean-all;
        inherit (project) sharedLib;
        inherit (repl) executable;
        default = repl.executable;
      };
      legacyPackages = {
        inherit project leanPkgs;
      };
      checks = {
        test = pkgs.runCommand "test" {
          buildInputs = [ test.executable leanPkgs.lean-all ];
        } ''
          #export LEAN_SRC_PATH="${./.}"
          ${test.executable}/bin/test > $out
        '';
      };
      devShells.default = pkgs.mkShell {
        buildInputs = [ leanPkgs.lean-all leanPkgs.lean ];
      };
    };
  };
}
