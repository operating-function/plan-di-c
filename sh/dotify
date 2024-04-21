#! /usr/bin/env nix-shell
#! nix-shell -i bash -p graphviz

DIR=$1

find $DIR -type f -name '*.dot' | sort | while IFS= read -r file; do
     in="$file"
     out="${file%.*}.png"
     dot -Tpng -o $out $in &
     echo "$in -> $out"
done

while wait -n; do : ; done; # wait until it's possible to wait for bg job
