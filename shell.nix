{ pkgs }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    gdb
    valgrind
  ];
}
