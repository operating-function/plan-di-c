#! /usr/bin/env nix-shell
#! nix-shell -i bash -p inotify-tools
#
compile () {
  clear
  make plan 2>&1 | head "-n$((`tput lines` - 12))"
}

compile

while
        inotifywait -e modify -e close_write -e move -e create .
do
        compile
done
