# Pillow vs ezimg bench: native Bend driver + Nix-embedded compare script.
# No checked-in *.py files — compare text lives in compare.nix and is written
# with pkgs.writeText at eval time.
{
  pkgs,
  lib,
  bend,
  bend-cc,
  # Flake `self` (repo root). Used only to copy ezimg/ + bench/main.bend.
  self,
}:

let
  llvm = pkgs.llvmPackages_19;

  # Sandbox-safe CC: nixpkgs clang (native ELF). Local `nix develop` still
  # exports CC=bend-cc for host-ld native builds; both are non-JS.
  drv = pkgs.stdenv.mkDerivation {
    pname = "ezimg-bench-drv";
    version = "0.1.0";
    dontUnpack = true;
    nativeBuildInputs = [ bend llvm.clang ];
    buildPhase = ''
      cp -r ${self}/ezimg ./ezimg
      mkdir -p bench
      cp ${./main.bend} bench/main.bend
      cd bench
      export CC=${llvm.clang}/bin/clang
      export BEND_NO_TELEMETRY=1
      bend main.bend -o ezimg-bench
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp ezimg-bench $out/bin/ezimg-bench
    '';
    meta = {
      description = "Native ELF driver for ezimg Pillow comparison benches";
      mainProgram = "ezimg-bench";
    };
  };

  compareText = import ./compare.nix { drvBin = "ezimg-bench"; };
  comparePy = pkgs.writeText "ezimg-pillow-compare.py" compareText;

  py = pkgs.python3.withPackages (ps: [ ps.pillow ]);

  makeRunner = mode: pkgs.writeShellApplication {
    name = if mode == "correctness" then "ezimg-pillow-check" else "ezimg-pillow-bench";
    runtimeInputs = [ drv py ];
    text = ''
      set -euo pipefail
      export EZIMG_BENCH_DRV=${drv}/bin/ezimg-bench
      export EZIMG_BENCH_WORK="''${EZIMG_BENCH_WORK:-$(mktemp -d)}"
      export EZIMG_BENCH_MODE=${mode}
      mkdir -p "$EZIMG_BENCH_WORK"
      exec ${py}/bin/python ${comparePy} "$@"
    '';
  };

  checkBin = makeRunner "correctness";
  benchBin = makeRunner "all";

  # Flake check: correctness must pass. Timing is not part of this derivation.
  pillowCheck = pkgs.runCommand "ezimg-pillow-compare" {
    nativeBuildInputs = [ checkBin ];
  } ''
    export EZIMG_BENCH_WORK="$PWD/work"
    mkdir -p "$EZIMG_BENCH_WORK"
    ezimg-pillow-check | tee $out
  '';
in
{
  inherit drv pillowCheck;
  packages = {
    ezimg-bench-drv = drv;
    ezimg-pillow-check = checkBin;
    ezimg-pillow-bench = benchBin;
  };
  apps = {
    pillow-check = {
      type = "app";
      program = "${checkBin}/bin/ezimg-pillow-check";
    };
    pillow-bench = {
      type = "app";
      program = "${benchBin}/bin/ezimg-pillow-bench";
    };
  };
  checks = {
    pillow = pillowCheck;
  };
}
