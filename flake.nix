{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShells = rec {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              gdb
              linuxPackages.perf
              valgrind
            ];
          };
        };

        packages = rec {
          default = pkgs.stdenv.mkDerivation {
            name = "plan";
            src = ./.;
            buildPhase = ''
              make plan
            '';
            installPhase = ''
              mkdir -p $out/bin
              cp plan $out/bin
            '';
          };
        };
      });
}
