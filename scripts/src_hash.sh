#!/bin/bash
# SHA-256 over everything that determines the build and the checks: the hand-written Lean sources
# (Veles.lean and Veles/**/*.lean except the generated certificate trees Cert15, LS4511, LS5612 and
# their top files), certs/SHA256SUMS (which pins the certificate files the generated trees come
# from), certgen/, scripts/, lean-toolchain and lakefile.toml. Same output on any machine with the
# same files.
cd "$(dirname "$0")/.."
{ echo Veles.lean; echo certs/SHA256SUMS; echo lean-toolchain; echo lakefile.toml
  find Veles -name '*.lean' ! -path 'Veles/Cert15/*' ! -path 'Veles/LS4511/*' ! -path 'Veles/LS5612/*' \
    ! -name Cert15.lean ! -name LS4511.lean ! -name LS5612.lean
  find certgen scripts -type f ! -name '*.pyc' ! -path '*/__pycache__/*'; } \
  | LC_ALL=C sort | while read -r f; do printf '%s\n' "$f"; cat "$f"; done | (sha256sum 2>/dev/null || shasum -a 256) | cut -d' ' -f1
