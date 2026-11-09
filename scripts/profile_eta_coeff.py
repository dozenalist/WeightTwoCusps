"""Prepare isolated eta_coeff instrumentation and summarize its measured phases.

Run with native Python from the project root. Generated Lean files and raw logs
live in .lake/eta-profile; production Lean modules are never modified.
"""

import argparse
import hashlib
import json
import re
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake" / "eta-profile"

INSTRUMENTATION = r'''
initialize etaProfileStats : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}
initialize etaProfileJobs : IO.Ref (Array Json) ← IO.mkRef #[]
initialize etaProfileWall : IO.Ref (String × Nat) ← IO.mkRef ("", 0)

private def etaProfileMeasure {α : Type} (label : String)
    (action : Unit → MetaM α) : MetaM α := do
  let started ← IO.monoNanosNow
  let result ← action ()
  let elapsed := (← IO.monoNanosNow) - started
  etaProfileStats.modify fun stats =>
    let (ns, calls) := stats[label]?.getD (0, 0)
    stats.insert label (ns + elapsed, calls + 1)
  return result

elab "eta_profile_begin" label:str : command => do
  etaProfileWall.set (label.getString, ← IO.monoNanosNow)

elab "eta_profile_end" : command => do
  let (label, started) ← etaProfileWall.get
  let elapsed := (← IO.monoNanosNow) - started
  logInfo m!"ETA_WALL {(Json.mkObj [("label", toJson label), ("ns", toJson elapsed)]).compress}"
'''

WRAPPER = r'''
elab "eta_coeff_profile" label:str : tactic => do
  etaProfileStats.set {}
  etaProfileJobs.set #[]
  let started ← IO.monoNanosNow
  Lean.Elab.Tactic.evalTactic (← `(tactic| eta_coeff_profile_core))
  let elapsed := (← IO.monoNanosNow) - started
  let phases := (← etaProfileStats.get).toList.map fun (key, ns, calls) =>
    (key, Json.mkObj [("ns", toJson ns), ("calls", toJson calls)])
  let record := Json.mkObj [("label", toJson label.getString),
    ("tactic_ns", toJson elapsed), ("phases", Json.mkObj phases),
    ("jobs", toJson (← etaProfileJobs.get))]
  logInfo m!"ETA_PROFILE {record.compress}"
'''


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f"Expected exactly one match: {old[:90]!r}")
    return text.replace(old, new, 1)


def prepare():
    OUT.mkdir(parents=True, exist_ok=True)
    original = (ROOT / "WeightTwoCusps/Tactic/EtaCoefficient.lean").read_text(encoding="utf-8")
    text = original.replace("WeightTwoCusps.Tactic", "WeightTwoCusps.EtaProfile")
    text = replace_once(text, "namespace WeightTwoCusps.EtaProfile\n",
                        "namespace WeightTwoCusps.EtaProfile\n" + INSTRUMENTATION)
    text = replace_once(text, "private def etaCheck (", "private def etaCheckCore (")
    text = replace_once(text, "private def etaClosedInt", r'''private def etaCheck (proposition : Expr) : MetaM Expr :=
  etaProfileMeasure "check.total" fun _ => etaCheckCore proposition

private def etaClosedInt''')
    text = replace_once(text,
        "  let name ← withOptions (Lean.Elab.async.set · false) <|\n    mkAuxLemma [] proposition proof",
        "  let name ← etaProfileMeasure \"check.kernel_aux\" fun _ =>\n    withOptions (Lean.Elab.async.set · false) <|\n      mkAuxLemma [] proposition proof")
    text, count = re.subn(
        r"(?m)^(\s*)let values := etaConvolveTables (.*)$",
        r'\1let values ← etaProfileMeasure "generate.convolution" fun _ =>\n\1  pure (etaConvolveTables \2)', text)
    if count != 3:
        raise RuntimeError(f"Expected 3 convolution generation sites, got {count}")
    text = replace_once(text,
        "  let base ← etaCertifyTable a p (etaEulerTable m p)",
        '  let euler ← etaProfileMeasure "generate.euler" fun _ => pure (etaEulerTable m p)\n'
        "  let base ← etaCertifyTable a p euler")
    text = replace_once(text, "    let values := etaInverseTable base.values p",
        '    let values ← etaProfileMeasure "generate.inverse" fun _ =>\n'
        "      pure (etaInverseTable base.values p)")
    text = replace_once(text, "private def etaUnitTable (", "private def etaUnitTableCore (")
    text = replace_once(text, "  let mut factors : List EtaCoefficientTable := []",
        "  let mut factors : List EtaCoefficientTable := []\n  let mut exponents : Array Json := #[]")
    text = replace_once(text, "    let table ← etaSignedPowerTable m exponent p",
        '    exponents := exponents.push (Json.arr #[toJson m, toJson (toString exponent)])\n'
        "    let table ← etaSignedPowerTable m exponent p")
    text = replace_once(text,
        "  return result\n\n/-- Evaluate an analytic eta-quotient coefficient",
        '''  etaProfileJobs.modify (·.push (Json.mkObj [("level", toJson N),
    ("precision", toJson p), ("exponents", toJson exponents),
    ("expected", toJson (result.values.map toString))]))
  return result

private def etaUnitTable (N : Nat) (r : Expr) (p : Nat) : MetaM EtaCoefficientTable :=
  etaProfileMeasure "table.total" fun _ => etaUnitTableCore N r p

/-- Evaluate an analytic eta-quotient coefficient''')
    text = replace_once(text, 'macro "eta_coeff" : tactic =>',
                        'macro "eta_coeff_profile_core" : tactic =>')
    text = replace_once(text, "end WeightTwoCusps.EtaProfile",
                        WRAPPER + "\nend WeightTwoCusps.EtaProfile")
    (OUT / "EtaCoefficientProfile.lean").write_text(text, encoding="utf-8")

    prefixes = (ROOT / "WeightTwoCusps/Levels/HasEtaQuotientBasis/462/Coefficients.lean").read_text(encoding="utf-8")
    prefixes = replace_once(prefixes, "module\n", "module\n\npublic import EtaCoefficientProfile\n")
    prefixes = replace_once(prefixes, "set_option maxRecDepth 4096",
                            "set_option Elab.async false\nset_option maxRecDepth 4096")
    pattern = r"(?m)^theorem (\S+)([\s\S]*? := by\s+)eta_coeff\b"
    def profile_theorem(match):
        label = match[1]
        return (f'eta_profile_begin "{label}"\n'
                f'theorem profile_{label}{match[2]}eta_coeff_profile "{label}"\neta_profile_end')
    prefixes, count = re.subn(pattern, profile_theorem, prefixes)
    if count != 89:
        raise RuntimeError(f"Expected 89 level-462 prefix statements, got {count}")
    (OUT / "Level462Profile.lean").write_text(prefixes, encoding="utf-8")

    benchmark = (ROOT / "WeightTwoCusps/Tactic/EtaCoefficientBenchmarks.lean").read_text(encoding="utf-8")
    benchmark = benchmark.replace("public import WeightTwoCusps.Tactic.EtaCoefficient",
                                  "public import EtaCoefficientProfile")
    benchmark = benchmark.replace("public section", "set_option Elab.async false\nset_option maxRecDepth 4096\npublic section")
    benchmark, count = re.subn(pattern, profile_theorem, benchmark)
    if count != 4:
        raise RuntimeError(f"Expected 4 tau statements, got {count}")
    benchmark = benchmark.replace("#print axioms eta_tau_", "#print axioms profile_eta_tau_")
    (OUT / "TauProfile.lean").write_text(benchmark, encoding="utf-8")
    baseline = (ROOT / "WeightTwoCusps/Tactic/EtaCoefficientBenchmarks.lean").read_text(encoding="utf-8")
    baseline = baseline.replace("module\n", "module\n\npublic import EtaCoefficientProfile\n", 1)
    baseline = baseline.replace("public section", "set_option Elab.async false\nset_option maxRecDepth 4096\npublic section")
    def baseline_theorem(match):
        label = match[1]
        return (f'eta_profile_begin "{label}"\n'
                f'theorem baseline_{label}{match[2]}eta_coeff\neta_profile_end')
    baseline, count = re.subn(pattern, baseline_theorem, baseline)
    if count != 4:
        raise RuntimeError(f"Expected 4 baseline tau statements, got {count}")
    baseline = baseline.replace("#print axioms eta_tau_", "#print axioms baseline_eta_tau_")
    (OUT / "TauBaseline.lean").write_text(baseline, encoding="utf-8")
    (OUT / "metadata.json").write_text(json.dumps({
        "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
        "level462_statements": 89, "tau_statements": 4,
        "timings": "monotonic nanoseconds; synchronous elaboration; default heartbeats",
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Prepared isolated profiling files in {OUT}")


def read_records(path, marker):
    # PowerShell's redirected native output can be UTF-16 or UTF-8.
    raw = path.read_bytes()
    encoding = "utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig"
    text = raw.decode(encoding)
    return [json.loads(line.split(marker, 1)[1]) for line in text.splitlines() if marker in line]


def summarize():
    results = {}
    for name in ("TauProfile", "Level462Profile"):
        path = OUT / f"{name}.log"
        if not path.exists():
            continue
        rows = read_records(path, "ETA_PROFILE ")
        walls = {r["label"]: r["ns"] for r in read_records(path, "ETA_WALL ")}
        for row in rows:
            row["declaration_ns"] = walls.get(row["label"])
            row["generation_ns"] = sum(v["ns"] for k, v in row["phases"].items() if k.startswith("generate."))
        results[name] = rows
        jobs = [dict(job, label=row["label"]) for row in rows for job in row["jobs"]]
        (OUT / f"{name}-sage-input.json").write_text(json.dumps({"jobs": jobs}), encoding="utf-8")
        total = sum(r["declaration_ns"] or r["tactic_ns"] for r in rows)
        generation = sum(r["generation_ns"] for r in rows)
        checks = sum(r["phases"].get("check.total", {}).get("ns", 0) for r in rows)
        print(f"{name}: {len(rows)} statements, declaration {total/1e9:.6f}s, "
              f"candidate generation {generation/1e9:.6f}s ({100*generation/total:.5f}%), "
              f"etaCheck {checks/1e9:.6f}s ({100*checks/total:.3f}%)")
        for r in rows if name == "TauProfile" else []:
            print(f"  {r['label']}: declaration {r['declaration_ns']/1e9:.6f}s; "
                  f"generation {r['generation_ns']/1e9:.6f}s; "
                  f"checks {r['phases'].get('check.total',{}).get('ns',0)/1e9:.6f}s")
    (OUT / "profiles.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    baseline_path = OUT / "TauBaseline.log"
    if baseline_path.exists():
        baseline = read_records(baseline_path, "ETA_WALL ")
        (OUT / "baseline.json").write_text(json.dumps(baseline, indent=2) + "\n", encoding="utf-8")
        print("Unmodified tau baseline:")
        for row in baseline:
            print(f"  {row['label']}: declaration {row['ns']/1e9:.6f}s")


def analyze():
    summarize()
    profiles = json.loads((OUT / "profiles.json").read_text(encoding="utf-8"))
    result = {"metadata": json.loads((OUT / "metadata.json").read_text(encoding="utf-8")),
              "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "method": "Serial declarations, two Lean threads, default heartbeats, maxRecDepth 4096.",
              "workloads": {}}
    source = (ROOT / "WeightTwoCusps/Tactic/EtaCoefficient.lean").read_text(encoding="utf-8")
    if hashlib.sha256(source.encode()).hexdigest() != result["metadata"]["source_sha256"]:
        raise RuntimeError("Production eta_coeff changed during profiling")
    for name, expected_count in (("TauProfile", 4), ("Level462Profile", 89)):
        rows = profiles[name]
        if len(rows) != expected_count or any(r["declaration_ns"] is None for r in rows):
            raise RuntimeError(f"Incomplete workload: {name}")
        per_case = []
        for row in rows:
            phases = row["phases"]
            per_case.append({"label": row["label"],
                "declaration_seconds": row["declaration_ns"] / 1e9,
                "tactic_seconds": row["tactic_ns"] / 1e9,
                "generation_seconds": row["generation_ns"] / 1e9,
                "check_seconds": phases.get("check.total", {}).get("ns", 0) / 1e9,
                "kernel_aux_seconds": phases.get("check.kernel_aux", {}).get("ns", 0) / 1e9,
                "check_calls": phases.get("check.total", {}).get("calls", 0),
                "unit_precisions": [job["precision"] for job in row["jobs"]]})
        total = sum(r["declaration_seconds"] for r in per_case)
        generation = sum(r["generation_seconds"] for r in per_case)
        check = sum(r["check_seconds"] for r in per_case)
        sage = json.loads((OUT / f"{name}-sage-summary.json").read_text(encoding="utf-8-sig"))
        fresh = sage["Fresh"]
        warm = sage["Warm"]
        if any(launch["Jobs"] != expected_count for launch in fresh) or warm["Jobs"] != expected_count:
            raise RuntimeError(f"Wrong Sage job count: {name}")
        fresh_wall = statistics.median(r["WallSeconds"] for r in fresh)
        warm_calc = statistics.median(r["calculation_ns"] / 1e9 for r in warm["Rounds"][1:])
        workload = {"declarations": expected_count,
            "serial_declaration_seconds": total,
            "candidate_generation_seconds": generation,
            "candidate_fraction_percent": 100 * generation / total,
            "etaCheck_seconds": check,
            "etaCheck_fraction_percent": 100 * check / total,
            "kernel_aux_seconds": sum(r["kernel_aux_seconds"] for r in per_case),
            "other_seconds": total - generation - check,
            "ideal_free_generation_speedup": total / (total - generation),
            "sage_fresh_batch_median_seconds": fresh_wall,
            "sage_fresh_import_median_seconds": statistics.median(r["SageImportNs"] / 1e9 for r in fresh),
            "sage_fresh_calculation_median_seconds": statistics.median(r["Rounds"][0]["calculation_ns"] / 1e9 for r in fresh),
            "sage_warm_calculation_median_seconds": warm_calc,
            "fresh_batch_modeled_delta_seconds": fresh_wall - generation,
            "warm_arithmetic_only_modeled_delta_seconds": warm_calc - generation,
            "check_halved_modeled_saving_seconds": check / 2,
            "check_halved_modeled_saving_percent": 50 * check / total,
            "sage_launches": fresh, "sage_warm": warm, "cases": per_case}
        result["workloads"][name] = workload
        print(f"{name}: ideal arithmetic-only saving {generation:.6f}s ({100*generation/total:.4f}%), "
              f"Sage batch {fresh_wall:.6f}s, modeled delta {fresh_wall-generation:+.6f}s, "
              f"warm arithmetic {warm_calc:.6f}s")
    baseline = json.loads((OUT / "baseline.json").read_text(encoding="utf-8"))
    if len(baseline) != 4:
        raise RuntimeError("Incomplete unmodified-tactic baseline")
    result["tau_baseline"] = baseline
    result["tau_controls"] = []
    for suffix, profile_path, baseline_path in (
        ("first", OUT / "repeats/TauProfile-run1.log", OUT / "repeats/TauBaseline-run1.log"),
        ("latest", OUT / "TauProfile.log", OUT / "TauBaseline.log"),
    ):
        if not profile_path.exists() or not baseline_path.exists():
            continue
        measured = {r["label"]: r for r in read_records(profile_path, "ETA_WALL ")}
        original = {r["label"]: r for r in read_records(baseline_path, "ETA_WALL ")}
        result["tau_controls"].append({"run": suffix, "cases": [
            {"label": label, "instrumented_seconds": row["ns"] / 1e9,
             "unmodified_seconds": original[label]["ns"] / 1e9,
             "relative_difference_percent": 100 * (row["ns"] / original[label]["ns"] - 1)}
            for label, row in measured.items()]})
    destination = ROOT / "benchmarks" / "eta-coeff"
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "results.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["prepare", "summarize", "analyze"])
    args = parser.parse_args()
    {"prepare": prepare, "summarize": summarize, "analyze": analyze}[args.action]()
