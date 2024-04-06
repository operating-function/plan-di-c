{ pkgs }:

pkgs.stdenv.mkDerivation {
  name = "plan";
  src = ./.;
  buildPhase = ''
    make plan
  '';
  installPhase = ''
    mkdir -p $out/bin
    cp plan $out/bin
  '';
}
