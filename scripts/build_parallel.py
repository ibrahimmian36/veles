#!/usr/bin/env python3
"""Compile Lean modules in dependency order, up to P at a time (for a large machine).

Usage: build_parallel.py [--skip-built] P Module [Module ...]
(--skip-built: keep an .olean newer than its source; for development only, never for the freeze.)   (modules as paths without .lean, e.g. Veles/Cert15/T3)
Dependencies are read from `import Veles...` lines among the given modules. Each compile is logged
to build/logs/<module>.log with wall time; each OK line reports the module's peak resident memory; the run stops at the first failure.
Requires LEAN_PATH to be set (Mathlib plus ./build)."""
import os, re, subprocess, sys, time, resource
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
args = sys.argv[1:]
SKIP = "--skip-built" in args
args = [a for a in args if a != "--skip-built"]
P = int(args[0]); mods = args[1:]
deps = {}
for m in mods:
    imps = re.findall(r"^(?:public |meta |private )*import (Veles[\w.]*)", open(m + ".lean").read(), re.M)
    need = {i.replace(".", "/") for i in imps}
    missing = need - set(mods)
    if missing:
        print(f"MISSING Veles import(s) of {m}: {sorted(missing)}"); sys.exit(1)
    deps[m] = need
done, running, failed = set(), {}, None
os.makedirs("build/logs", exist_ok=True)
def compile_one(m):
    ole = f"build/{m}.olean"
    if SKIP and os.path.exists(ole) and os.path.getmtime(ole) > os.path.getmtime(m + ".lean"):
        return m, True, -1.0, 0.0
    os.makedirs(os.path.dirname("build/" + m), exist_ok=True)
    t0 = time.time()
    logf = open(f"build/logs/{m.replace('/', '_')}.out", "w")
    pr = subprocess.Popen(["lean", "--root=.", "-o", f"build/{m}.olean", "-i", f"build/{m}.ilean", f"{m}.lean"],
                          stdout=logf, stderr=subprocess.STDOUT)
    _, status, ru = os.wait4(pr.pid, 0)
    pr.returncode = os.waitstatus_to_exitcode(status); logf.close()
    rss_gib = ru.ru_maxrss / (1024 ** 3 if sys.platform == "darwin" else 1024 ** 2)   # bytes on macOS, KiB on Linux
    out = open(f"build/logs/{m.replace('/', '_')}.out").read() + f"\nEXIT={pr.returncode}"
    ok = pr.returncode == 0
    with open(f"build/logs/{m.replace('/', '_')}.log", "w") as fh:
        fh.write(out + f"\nWALL {time.time() - t0:.1f}s\n")
    return m, ok, time.time() - t0, rss_gib
start = time.time(); peak = 0.0
with ThreadPoolExecutor(P) as ex:
    pending = set(mods)
    while pending or running:
        ready = [m for m in pending if deps[m] <= done]
        for m in ready[: P - len(running)]:
            pending.discard(m); running[ex.submit(compile_one, m)] = m
        if not running:
            print("DEPENDENCY DEADLOCK", pending); sys.exit(1)
        fin, _ = wait(list(running), return_when=FIRST_COMPLETED)
        for fu in fin:
            m, ok, dt, rss = fu.result(); del running[fu]; peak = max(peak, rss)
            print(f"{'OK ' if ok else 'FAIL'} {m} {'reused' if dt < 0 else f'{dt:.0f}s {rss:.1f}GiB'}  ({len(done) + 1}/{len(mods)}, {time.time() - start:.0f}s)", flush=True)
            if not ok:
                print(open(f"build/logs/{m.replace('/', '_')}.log").read()[-3000:]); sys.exit(1)
            done.add(m)
print(f"ALL OK {len(mods)} modules in {time.time() - start:.0f}s")
print(f"PEAK RSS {peak:.1f} GiB (largest resident memory of any one module build)")
