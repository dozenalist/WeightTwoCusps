"""Measure Sage candidate arithmetic only; this script establishes no Lean proof.

Run under the existing Sage/WSL Python, receiving the profiling jobs on stdin.
Every output prefix is compared with the independently kernel-checked Lean
result. Startup/import, arithmetic, validation, and JSON encoding are separate.
"""

import json
import sys
import time

started = time.perf_counter_ns()
request = json.load(sys.stdin)
parsed = time.perf_counter_ns()
from sage.all import PowerSeriesRing, ZZ
from sage.env import SAGE_VERSION
imported = time.perf_counter_ns()


def euler_table(dilation, precision):
    values = [0] * precision
    values[0] = 1
    for k in range(1, precision + 1):
        a = dilation * k * (3 * k - 1) // 2
        b = dilation * k * (3 * k + 1) // 2
        if a >= precision:
            break
        value = -1 if k % 2 else 1
        values[a] = value
        if b < precision:
            values[b] = value
    return values


def calculate(job):
    precision = int(job["precision"])
    if precision == 0:
        return []
    ring = PowerSeriesRing(ZZ, "q", default_prec=precision)
    value = ring(1).add_bigoh(precision)
    for dilation, exponent in job["exponents"]:
        exponent = int(exponent)
        if exponent:
            factor = ring(euler_table(int(dilation), precision)).add_bigoh(precision)
            value *= factor ** exponent
    return [str(value[i]) for i in range(precision)]


rounds = []
outputs = []
for _ in range(int(request.get("rounds", 3))):
    before = time.perf_counter_ns()
    outputs = [calculate(job) for job in request["jobs"]]
    calculated = time.perf_counter_ns()
    for job, output in zip(request["jobs"], outputs):
        expected = job["expected"][:job["precision"]]
        expected += ["0"] * (job["precision"] - len(expected))
        if output != expected:
            raise ValueError(f"Sage/Lean candidate mismatch for {job['label']}")
    verified = time.perf_counter_ns()
    rounds.append({"calculation_ns": calculated - before,
                   "comparison_ns": verified - calculated})

result = {"status": "ok", "sage_version": SAGE_VERSION,
          "jobs": len(request["jobs"]), "input_parse_ns": parsed - started,
          "sage_import_ns": imported - parsed, "rounds": rounds,
          "outputs": outputs}
before_encode = time.perf_counter_ns()
encoded = json.dumps(result, separators=(",", ":"))
result["initial_json_encode_ns"] = time.perf_counter_ns() - before_encode
result["initial_json_bytes"] = len(encoded.encode("utf-8"))
print(json.dumps(result, separators=(",", ":")))
