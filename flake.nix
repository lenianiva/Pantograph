{
  description = "Pantograph";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix?ref=157c85903f668fadeb79f330961b7bbe5ee596de";
    lspec = {
      url = "github:argumentcomputer/LSpec?ref=504a8cecf8da601b9466ac727aebb6b511aae4ab";
      flake = false;
    };
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    lean4-nix,
    lspec,
    ...
  } : flake-parts.lib.mkFlake { inherit inputs; } {
    flake = {
    };
    systems = [
      "aarch64-linux"
      "aarch64-darwin"
      "x86_64-linux"
      "x86_64-darwin"
    ];
    perSystem = { system, pkgs, ... }: let
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
      };
      systems = [
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-linux"
        "x86_64-darwin"
      ];
      perSystem = {
        system,
        pkgs,
        ...
      }: let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };
        lspecLib = pkgs.lean.buildLeanPackage {
          name = "LSpec";
          roots = ["Main" "LSpec"];
          src = "${lspec}";
        };
        project = pkgs.lean.buildLeanPackage {
          name = "Pantograph";
          roots = ["Pantograph"];
          src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              !(pkgs.lib.hasInfix "/Test/" path)
              && !(pkgs.lib.hasSuffix ".md" path)
              && !(pkgs.lib.hasSuffix "Repl.lean" path);
          });
        };
        repl = pkgs.lean.buildLeanPackage {
          name = "Repl";
          roots = ["Main" "Repl"];
          deps = [project];
          src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              !(pkgs.lib.hasInfix "/Test/" path)
              && !(pkgs.lib.hasSuffix ".md" path);
          });
        };
        test = pkgs.lean.buildLeanPackage {
          name = "Test";
          # NOTE: The src directory must be ./. since that is where the import
          # root begins (e.g. `import Test.Environment` and not `import
          # Environment`) and thats where `lakefile.lean` resides.
          roots = ["Test.Main"];
          deps = [lspecLib repl];
          src = pkgs.lib.cleanSource (pkgs.lib.cleanSourceWith {
            src = ./.;
            filter = path: type:
              !(pkgs.lib.hasInfix "Pantograph" path);
          });
        };
      in rec {
        packages = {
          inherit (pkgs.lean) lean lean-all;
          inherit (project) sharedLib iTree;
          inherit (repl) executable;
          default = repl.executable;
        };
        formatter = pkgs.alejandra;
        legacyPackages = {
          inherit project;
          leanPkgs = pkgs.lean;
        };
        checks = {
          test =
            pkgs.runCommand "test" {
              buildInputs = [test.executable pkgs.lean.lean-all];
            } ''
              #export LEAN_SRC_PATH="${./.}"
              ${test.executable}/bin/test > $out
            '';
        };
        devShells.default = pkgs.mkShell {
          buildInputs = [pkgs.lean.lean-all pkgs.lean.lean];
        };
      };
    };
}
