#!/usr/bin/env bash
# usage: build.sh <label>  : いまの作業ツリーをビルドして bin/<label> に置く。
# 古いバイナリで測ってしまう事故を防ぐため、ベンチは必ずこれを通して用意する。
set -eu
S=$(cd "$(dirname "$0")" && pwd)
cd ~/Geometry-Solver
cargo build --release 2>&1 | grep -E "^(error|warning: unused)" || true
cargo build --release 2>&1 | tail -1
cp -f target/release/geom_solver "$S/bin/$1"
echo "bin/$1  <-  $(git rev-parse --short HEAD)$(git diff --quiet || echo '+dirty')  md5=$(md5sum "$S/bin/$1" | cut -c1-12)"
