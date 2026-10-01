#!/bin/bash
# SHA-256 over the generated certificate modules (Veles/Cert15, LS4511, LS5612 and their top files),
# so a gate log records exactly which emitted modules it built.
cd "$(dirname "$0")/.."
{ ls Veles/Cert15.lean Veles/LS4511.lean Veles/LS5612.lean
  find Veles/Cert15 Veles/LS4511 Veles/LS5612 -name '*.lean'; } 2>/dev/null \
  | LC_ALL=C sort | while read -r f; do printf '%s\n' "$f"; cat "$f"; done | (sha256sum 2>/dev/null || shasum -a 256) | cut -d' ' -f1
