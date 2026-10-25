#!/bin/sh
# Records the expected output of each run-pass test from rustc (the reference).
#   tests/bless.sh [test.rs…]
set -e
cd "$(dirname "$0")/run-pass"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
files=${*:-*.rs}
for f in $files; do
    f=$(basename "$f")
    name=${f%.rs}
    RUSTC_BOOTSTRAP=1 rustc --edition 2021 --crate-type bin -C overflow-checks=off -C panic=abort \
        -C link-arg=-lc -A warnings "$f" -o "$tmp/$name"
    "$tmp/$name" > "$name.stdout"
    echo "blessed $name"
done
