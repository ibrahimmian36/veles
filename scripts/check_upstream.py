#!/usr/bin/env python3
"""Test that the copied formal-conjectures material is verbatim.

1. The saved upstream files (upstream/) have their pinned SHA-256 hashes and git blob
   SHA-1s; the blob SHA-1s are those GitHub reports for commit
   137aec5c7abd3aa61f7a73138a97279acfc79e93 (checked on 30 September 2026 through the contents API).
2. Veles/Upstream.lean and Veles/UpstreamComposite.lean are regenerated here from the upstream
   files (declaration blocks cut out verbatim, each block required to occur exactly once) and
   compared with the repository files byte for byte, so nothing can be added between blocks.
3. The statements of Veles/Results.lean `Fills` (text up to `:=`) equal upstream's, and
   Veles/Tests/UpstreamStatements.lean (written with --write-statements) re-elaborates each upstream
   statement verbatim in upstream's context and closes it with the Fills theorem.
Controls: a one-character change inside a block, a line inserted between blocks, and a changed
Fills statement must each be caught. Exit 0 on PASS."""
import hashlib, os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
U = os.path.join(ROOT, "upstream")
F_J = "FormalConjecturesForMathlib_Combinatorics_SimpleGraph_Johnson.lean"
F_E = "FormalConjectures_ErdosProblems_835.lean"
F_S = "FormalConjectures_Wikipedia_SteinerSystem.lean"
F_C = "FormalConjecturesForMathlib_Data_Nat_Prime_Composite.lean"
F_Q = "FormalConjecturesForMathlib_Combinatorics_SimpleGraph_Clique.lean"
PINS = {  # file: (sha256, git blob sha1 at 137aec5)
    F_J: ("96c424d37a2a575fc083bf368dcfd4f434bebf4548b59d3a9fd8e6459452d562", "1b8504f2ce8efbbadd3f716d3ef065e5bff2ad58"),
    F_E: ("78d49e65a75a008aefc8b64817900da0d5c097fc6e62ecfb6f25ed243be56fa5", "ac6e96c92259f902b895e8196d1b1da425769bd9"),
    F_S: ("cb59c262633a8b4952fb978048afc8f2ad4030180e3948a5782a16aa7dbf225d", "e57ff36f646eb3cc71a522ec6bfaf9956b04a2c3"),
    F_C: ("2863dd196d1207569df4557a1f504e6bfb538a7c82b1955529b4a312f0f7106e", "11eab3a333e56f6a20e9447e7334350c7a3329f4"),
    F_Q: ("2773977ef2ecc759e0b5dc15c692e80de14d2f9db37ba28b8f692cc078a4dd53", "cb50337539bb774b130d42315b794203a614e012"),
}
FILLS = ["theorem property_iff_chromaticNumber", "theorem johnsonGraph_2k_k_chromaticNumber_known_cases",
         "theorem johnsonGraph_18_9_chromaticNumber", "lemma indepNum_johnson_le_johnsonBound",
         "theorem chromaticNumber_johnson_2k_k_lower_bound ", "theorem johnson_chromaticNumber_odd",
         "theorem johnson_chromaticNumber_composite"]

# The module docstrings of the two copy files, pinned literally: nothing else may precede the
# copied blocks, and a docstring cannot close early and hide code.
MODDOC_UP = '/-!\n# Upstream definitions\n\nCopied verbatim from google-deepmind/formal-conjectures (Apache-2.0, notice above),\ncommit 137aec5c7abd3aa61f7a73138a97279acfc79e93 (snapshots in `upstream/`):\n\n* `SimpleGraph.johnson` and the `J(n, k)` notation, from\n  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean`;\n* `Erdos835.Property` and `Erdos835.johnsonBound`, from\n  `FormalConjectures/ErdosProblems/835.lean`;\n* `SteinerSystems.SteinerSystem`, the `S(t, k, n)` notation and\n  `SteinerSystems.LargeSteinerSystemWitness`, from\n  `FormalConjectures/Wikipedia/SteinerSystem.lean`.\n\nChanges: the module header, `public import` lines and `@[expose] public section`\nare dropped, and `import Mathlib` replaces the upstream imports. Every copied\ndeclaration block is byte-identical to upstream; `scripts/check_upstream.py`\ntests this.\n-/\n'
MODDOC_COMP = '/-!\n# Upstream `Nat.Composite`\n\nCopied verbatim from google-deepmind/formal-conjectures (Apache-2.0, notice above), commit\n137aec5c7abd3aa61f7a73138a97279acfc79e93: `Nat.Composite` from\n`FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`, and the notation `α(G)` for the\nindependence number from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean`.\nOnly these lines are copied; `scripts/check_upstream.py` tests that each is byte-identical.\n-/\n'

def rd(f): return open(os.path.join(U, f), encoding="utf-8").read()

def once(text, start, end, back_to_doc=True):
    assert text.count(start) == 1, f"marker not unique: {start!r}"
    i = text.index(start)
    if back_to_doc:
        i = text.rfind("\n", 0, i) + 1
        if text[max(0, i - 4):i] == "/--\n": i -= 4
    j = text.index(end, i) + len(end)
    return text[i:j]

def header(text): return text.split("-/", 1)[0] + "-/\n"

def expected_upstream():
    J, E, S = rd(F_J), rd(F_E), rd(F_S)
    johnson = once(J, "The Johnson graph $J(n, k)$", 'scoped notation "J(" n ", " k ")" => johnson n k') + "\n\n"
    prop = once(E, "The property that for a given $k$", "(univ : Finset (Fin (k+1)))\n")
    jb = once(E, "/-- Johnson's upper bound", "(n + 1) * johnsonBound n d w / (w + 1)\n", back_to_doc=False)
    ss = once(S, "An $S(t, k, n)$-Steiner system is", "  system : S(t, k, n)\n")
    moddoc = MODDOC_UP
    return (f"{header(E)}import Mathlib\n\n{moddoc}\nopen Finset\n\nnamespace SimpleGraph\nvariable {{n k : ℕ}}\n\n"
            f"{johnson}end SimpleGraph\n\nopen SimpleGraph\nopen scoped Nat\nnamespace Erdos835\n\nvariable {{n k : ℕ}}\n\n"
            f"{prop}\n{jb}\nend Erdos835\n\nnamespace SteinerSystems\n\n{ss}\nend SteinerSystems\n")

def expected_composite():
    C, Q = rd(F_C), rd(F_Q)
    comp = once(C, "abbrev Nat.Composite", "¬n.Prime", back_to_doc=False)
    alpha = once(Q, '@[inherit_doc] scoped notation "α("', "=> indepNum G", back_to_doc=False)
    moddoc = MODDOC_COMP
    return (f"{header(C)}import Mathlib\n\n{moddoc}\n{comp}\n\nnamespace SimpleGraph\n\n{alpha}\n\nend SimpleGraph\n")

def split_decl(up, kw, name):
    """Split `kw name BINDERS : STMT :=` at the first top-level colon."""
    rest = up[len(f"{kw} {name}"):]
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "([{⟨": depth += 1
        elif ch in ")]}⟩": depth -= 1
        elif ch == ":" and depth == 0 and rest[i + 1:i + 2] != "=":
            return rest[:i].strip(), rest[i + 1:].rstrip()[:-2].strip()
    raise AssertionError(f"cannot split {name}")

def stmt_parts():
    E = rd(F_E); parts = []
    for head in FILLS:
        kw, name = head.split()[0], head.split()[1]
        up = once(E, head, ":=", back_to_doc=False)
        binders, stmt = split_decl(up, kw, name)
        free = [v for v in ("n", "k") if re.search(r"(?<![\w'])" + v + r"(?![\w'])", stmt) and
                not re.search(r"\(\s*" + v + r"\s*:", binders)]
        parts.append((name, binders, stmt, free))
    return parts

PRE = "open Finset SimpleGraph\nopen scoped Nat\nnamespace Erdos835\n\n"

def expected_types():
    """Veles/Tests/UpstreamTypes.lean: each upstream statement, verbatim, closed over its binders and
    elaborated with only the copied upstream definitions (and Mathlib) in scope."""
    E = rd(F_E)
    out = [header(E), "import Veles.Upstream\nimport Veles.UpstreamComposite\n\n",
           "/-! Generated by `scripts/check_upstream.py`. Each `Prop` below is a formal-conjectures\n",
           "statement, verbatim, closed over its binders, elaborated with only the copied upstream\n",
           "definitions in scope (no other module of this repository is imported). -/\n\n", PRE]
    for name, binders, stmt, free in stmt_parts():
        bs = (("{" + " ".join(free) + " : ℕ} ") if free else "") + binders
        out.append(f"/-- `{name}` -/\nabbrev type_{name} : Prop :=\n  ∀ {bs},\n    {stmt}\n\n" if bs.strip()
                   else f"/-- `{name}` -/\nabbrev type_{name} : Prop :=\n    {stmt}\n\n")
    out.append("end Erdos835\n")
    return "".join(out)

def expected_statements():
    """Veles/Tests/UpstreamStatements.lean: each upstream statement type proved by our theorem."""
    E = rd(F_E)
    out = [header(E), "import Veles.Tests.UpstreamTypes\nimport Veles.Results\n\n",
           "/-! Generated by `scripts/check_upstream.py`. Each formal-conjectures statement, as elaborated\n",
           "in `Veles.Tests.UpstreamTypes`, is proved by the corresponding theorem of\n",
           "`Veles.Results.Fills`; the kernel checks that the types agree. -/\n\nnamespace Erdos835\n\n"]
    for name, binders, stmt, free in stmt_parts():
        out.append(f"theorem upstream_{name} : type_{name} := by\n  intros\n  apply Veles.Results.Fills.{name} <;> assumption\n\n")
    out.append("end Erdos835\n")
    return "".join(out)

def fills_ok(results):
    E, bad = rd(F_E), []
    for head in FILLS:
        up = once(E, head, ":=", back_to_doc=False)
        if results.count(up) != 1: bad.append(head)
    return bad

def check(up_text, comp_text, results):
    bad = []
    for f, (h256, blob) in PINS.items():
        d = open(os.path.join(U, f), "rb").read()
        if hashlib.sha256(d).hexdigest() != h256: bad.append(f"sha256 {f}")
        if hashlib.sha1(b"blob %d\0" % len(d) + d).hexdigest() != blob: bad.append(f"blob {f}")
    try:
        if up_text != expected_upstream(): bad.append("Veles/Upstream.lean differs from the regenerated copy")
        if comp_text != expected_composite(): bad.append("Veles/UpstreamComposite.lean differs from the regenerated copy")
    except AssertionError as e:
        bad.append(str(e))
    bad += [f"Fills statement differs: {h}" for h in fills_ok(results)]
    for fn, gen in (("Veles/Tests/UpstreamTypes.lean", expected_types), ("Veles/Tests/UpstreamStatements.lean", expected_statements)):
        fp = os.path.join(ROOT, fn)
        if not os.path.exists(fp) or open(fp, encoding="utf-8").read() != gen():
            bad.append(f"{fn} differs from the regenerated file")
    return bad

if __name__ == "__main__":
    if "--write-statements" in sys.argv:
        open(os.path.join(ROOT, "Veles/Tests/UpstreamTypes.lean"), "w", encoding="utf-8").write(expected_types())
        open(os.path.join(ROOT, "Veles/Tests/UpstreamStatements.lean"), "w", encoding="utf-8").write(expected_statements())
    up = open(os.path.join(ROOT, "Veles/Upstream.lean"), encoding="utf-8").read()
    comp = open(os.path.join(ROOT, "Veles/UpstreamComposite.lean"), encoding="utf-8").read()
    res = open(os.path.join(ROOT, "Veles/Results.lean"), encoding="utf-8").read()
    bad = check(up, comp, res)
    controls = [
        (up.replace("#(s.val ∩ t.val) + 1 = k", "#(s.val ∩ t.val) + 1 = k + 0", 1), comp, res),
        (up.replace("end SimpleGraph", "attribute [-simp] Finset.card_eq_zero\nend SimpleGraph", 1), comp, res),
        (up, comp, res.replace("(hk : 3 ≤ k) (hk' : k ≤ 8) :\n    k + 1 <", "(hk : 3 ≤ k) (hk' : k ≤ 9) :\n    k + 1 <", 1)),
        (up.replace("tests this.\n-/\n", "tests this. -/\nmacro_rules | `(Finset.univ) => `((∅ : Finset _))\n/- reopen\n-/\n", 1), comp, res),
    ]
    for i, c in enumerate(controls):
        if c == (up, comp, res) or len(check(*c)) <= len(bad):
            print(f"CONTROL {i} FAIL: not caught"); sys.exit(1)
    for b in bad: print(b)
    print(f"UPSTREAM CHECK: {'FAIL' if bad else 'PASS'} ({len(PINS)} files pinned by sha256 and git blob, "
          f"2 copies regenerated, {len(FILLS)} statements; {len(controls)} controls caught)")
    sys.exit(1 if bad else 0)
