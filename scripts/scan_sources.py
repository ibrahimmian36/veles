#!/usr/bin/env python3
"""Reject forbidden constructs in every Lean source under Veles/ and in Veles.lean.

A small lexer removes comments (nested `/- -/`, line `--`) and string and character literals, so
neither can hide or fake a token. Then, anywhere in the remaining code:
  * tokens: sorry, admit, native_decide, bv_decide, bv_check, implemented_by, extern, sorryAx,
    ofReduceBool, ofReduceNat, skipKernelTC, addDecl, addDeclWithoutChecking, modifyEnv, setEnv,
    run_cmd, run_elab, run_meta, run_tac, #eval, elab, elab_rules, macro, macro_rules, syntax,
    initialize, builtin_initialize, command_elab, term_elab, tactic, Kernel;
  * declarations: axiom, opaque, unsafe, and `notation`/`infix`/`prefix`/`postfix`.
Allowed exceptions: Veles/AxiomAudit.lean may use run_cmd; the copied upstream files may declare
their three notations. Controls: every rule is exercised on a planted probe and must fire, and a
token inside a comment or a string must not. Exit 0 when clean."""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOKENS = ["sorry", "admit", "native_decide", "bv_decide", "bv_check", "implemented_by", "extern",
          "sorryAx", "ofReduceBool", "ofReduceNat", "skipKernelTC", "addDecl", "addDeclWithoutChecking",
          "modifyEnv", "setEnv", "run_cmd", "run_elab", "run_meta", "run_tac", "#eval", "elab",
          "elab_rules", "macro", "macro_rules", "syntax", "initialize", "builtin_initialize",
          "command_elab", "term_elab", "tactic", "Kernel"]
DECL = re.compile(r"(?:^|[\s\]])(axiom|opaque|unsafe|notation|infix|infixl|infixr|prefix|postfix)\b")
ALLOW = {"Veles/AxiomAudit.lean": {"run_cmd"},
         "Veles/Upstream.lean": {"notation"}, "Veles/UpstreamComposite.lean": {"notation"}}

def strip(src):
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i): depth, i = depth + 1, i + 2
                elif src.startswith("-/", i): depth, i = depth - 1, i + 2
                else: i += 1
            out.append(" ")
        elif src.startswith("--", i):
            while i < n and src[i] != "\n": i += 1
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1; out.append(' "" ')
        elif src[i] == "'" and i + 2 < n and (src[i + 2] == "'" or src[i + 1] == "\\"):
            j = src.find("'", i + 2); i = (j + 1) if j > 0 else i + 1; out.append(" c ")
        else:
            out.append(src[i]); i += 1
    return "".join(out)

def scan(text, rel="X.lean"):
    body = strip(text); allow = ALLOW.get(rel, set()); hits = []
    for t in TOKENS:
        pat = (r"(?<![\w])" if not t.startswith("#") else r"(?<!\S)") + re.escape(t) + r"(?![\w])"
        if re.search(pat, body) and t not in allow: hits.append(t)
    for m in DECL.finditer(body):
        if m.group(1) not in allow: hits.append(m.group(1) + " declaration")
    return hits

PROBES = ["theorem x : True := by sorry", "open Lean in run_cmd pure ()", "open Lean in #eval 1",
          "elab_rules : command | _ => Lean.modifyEnv id", "@[command_elab foo] def f := 1",
          "local elab \"x\" : command => pure ()", "macro_rules | `(tactic| decide) => `(tactic| rfl)",
          "theorem t : False := sorryAx _ false", "theorem t := @Lean.ofReduceNat", "axiom foo : False",
          "opaque x : Nat", "unsafe def f := 1", "scoped notation \"Q\" => 1", "x := Lean.Kernel.Environment.addDeclWithoutChecking",
          "by run_tac pure ()"]
QUIET = ["/- sorry run_cmd -/ theorem a : True := trivial", "-- sorry\ndef s : String := \"sorry run_cmd /-\"\ndef t := 1"]

if __name__ == "__main__":
    for p in PROBES:
        if not scan(p + "\n"):
            print("CONTROL FAIL: probe not caught:", p); sys.exit(1)
    for q in QUIET:
        if scan(q + "\n"):
            print("CONTROL FAIL: false hit in comment/string:", repr(q), scan(q + "\n")); sys.exit(1)
    files = ["Veles.lean"] + sorted(os.path.relpath(os.path.join(d, f), ROOT)
                                    for d, _, fs in os.walk(os.path.join(ROOT, "Veles")) for f in fs if f.endswith(".lean"))
    bad = [(f, h) for f in files for h in [scan(open(os.path.join(ROOT, f), encoding="utf-8").read(), f)] if h]
    for f, h in bad: print(f"{f}: {h}")
    print(f"SOURCE SCAN: {'FAIL' if bad else 'PASS'} ({len(files)} files; {len(PROBES)} probes caught, {len(QUIET)} quiet controls)")
    sys.exit(1 if bad else 0)
