{ pkgs }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    gdb
    linuxPackages.perf
    valgrind
  ];
}
