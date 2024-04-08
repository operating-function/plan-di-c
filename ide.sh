#! /usr/bin/env nix-shell
#! nix-shell -i bash -p inotify-tools

clear
make plan

while
        inotifywait -e modify -e close_write -e move -e create .
do
        clear
        make plan
done
