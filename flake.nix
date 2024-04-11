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
          plankShell = import ./shell.nix { inherit pkgs; };
          default = plankShell;
        };

        packages = rec {
          plank = import ./default.nix { inherit pkgs; };
          default = plank;
        };
      });
}
