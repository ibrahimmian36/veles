/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles

/-! # Automated whole-library axiom audit

Walks every module under `Veles.*` in the compiled environment, finds every theorem,
definition and opaque constant, recomputes each axiom closure, and refuses to compile unless everything
depends on at most `propext`, `Classical.choice` and `Quot.sound`. Any `axiom` declaration
in a `Veles` module fails the audit. `sorryAx` and the axioms minted by native evaluation
(`Lean.ofReduceBool`, `Lean.ofReduceNat`) lie outside the allowed set, so either fails this
file by construction. `scripts/pod_gate.sh` requires this audit and the manifest
`Veles/AxiomCheck.lean` to pass.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut thms : Nat := 0
  let mut defs : Nat := 0
  let mut offenders : Array (Name × Array Name) := #[]
  let mut axiomDecls : Array Name := #[]
  for (modName, modData) in env.header.moduleNames.zip env.header.moduleData do
    unless Name.isPrefixOf `Veles modName do continue
    for declName in modData.constNames do
      match env.find? declName with
      | some (.thmInfo _) =>
        let bad := (← collectAxioms declName).filter (fun ax => !allowed.contains ax)
        thms := thms + 1
        unless bad.isEmpty do offenders := offenders.push (declName, bad)
      | some (.defnInfo _) =>
        let bad := (← collectAxioms declName).filter (fun ax => !allowed.contains ax)
        defs := defs + 1
        unless bad.isEmpty do offenders := offenders.push (declName, bad)
      | some (.opaqueInfo _) =>
        let bad := (← collectAxioms declName).filter (fun ax => !allowed.contains ax)
        defs := defs + 1
        unless bad.isEmpty do offenders := offenders.push (declName, bad)
      | some (.axiomInfo _) => axiomDecls := axiomDecls.push declName
      | _ => pure ()
  unless axiomDecls.isEmpty do
    throwError "AXIOM AUDIT: FAIL: axiom declarations in Veles modules: {axiomDecls}"
  unless offenders.isEmpty do
    throwError "AXIOM AUDIT: FAIL: {offenders.size} declaration(s) beyond the allowed axioms: {offenders}"
  if thms == 0 then
    throwError "AXIOM AUDIT: FAIL: scanned zero theorems, the module filter is broken"
  logInfo m!"AXIOM AUDIT: PASS: {thms} theorems and {defs} definitions across all Veles modules, axioms within {allowed}"
