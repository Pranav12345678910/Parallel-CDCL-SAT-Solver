#!/usr/bin/env python3
import argparse
import csv
import os
import statistics
import subprocess
import time
from pathlib import Path

def run_once(solver, testcase, threads=None, timeout=None):
    env = os.environ.copy()
    if threads is not None:
        env["OMP_NUM_THREADS"] = str(threads)
    start = time.perf_counter()
    proc = subprocess.run(
        [str(solver), str(testcase)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        timeout=timeout
    )
    elapsed = time.perf_counter() - start
    return {
        "returncode": proc.returncode,
        "seconds": elapsed,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }

def classify(stdout):
    if "UNSAT" in stdout.upper():
        return "UNSAT"
    if "SATISFIABLE" in stdout.upper():
        return "SAT"
    return "UNKNOWN"

def natural_key(path):
    import re
    return [int(x) if x.isdigit() else x.lower() for x in re.split(r'(\d+)', path.name)]

def main():
    parser = argparse.ArgumentParser(description="Benchmark SAT solver over every test file in ../tests.")
    parser.add_argument("solver", help="Path to compiled solver binary")
    parser.add_argument("--tests-dir", default="../tests", help="Directory containing .txt test cases")
    parser.add_argument("--threads", nargs="+", type=int, default=[1], help="OMP thread counts to test")
    parser.add_argument("--repeats", type=int, default=3, help="Runs per test/thread combination")
    parser.add_argument("--timeout", type=float, default=None, help="Per-run timeout in seconds")
    parser.add_argument("--csv", default="benchmark_results.csv", help="Output CSV path")
    args = parser.parse_args()

    solver = Path(args.solver).resolve()
    tests_dir = Path(args.tests_dir)
    tests = sorted(tests_dir.glob("*.txt"), key=natural_key)

    if not solver.exists():
        raise SystemExit(f"Solver not found: {solver}")
    if not tests:
        raise SystemExit(f"No .txt tests found in {tests_dir}")

    print(f"Solver: {solver}")
    print(f"Tests dir: {tests_dir.resolve()}")
    print(f"Found {len(tests)} test files")
    print()
    print("IMPORTANT: if your C++ code still calls omp_set_num_threads(1),")
    print("the --threads values here will NOT change thread count.")
    print("Remove that hardcoded line or replace it with env/argv-based control.")
    print()

    rows = []
    for testcase in tests:
        for threads in args.threads:
            times = []
            statuses = []
            timed_out = False
            print(f"Running {testcase.name} with {threads} thread(s)...", flush=True)
            for r in range(args.repeats):
                try:
                    result = run_once(solver, testcase, threads=threads, timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    print(f"  repeat {r+1}: TIMEOUT")
                    break

                status = classify(result["stdout"])
                times.append(result["seconds"])
                statuses.append(status)
                print(f"  repeat {r+1}: {result['seconds']:.4f}s  status={status}  rc={result['returncode']}")

                rows.append({
                    "testcase": testcase.name,
                    "threads": threads,
                    "repeat": r + 1,
                    "seconds": result["seconds"],
                    "status": status,
                    "returncode": result["returncode"],
                    "stdout": result["stdout"].strip(),
                    "stderr": result["stderr"].strip(),
                })

            if timed_out:
                rows.append({
                    "testcase": testcase.name,
                    "threads": threads,
                    "repeat": "timeout",
                    "seconds": "",
                    "status": "TIMEOUT",
                    "returncode": "",
                    "stdout": "",
                    "stderr": "",
                })
                continue

            if times:
                avg = statistics.mean(times)
                med = statistics.median(times)
                print(f"  avg={avg:.4f}s  median={med:.4f}s")
            print()

    csv_path = Path(args.csv)
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=["testcase", "threads", "repeat", "seconds", "status", "returncode", "stdout", "stderr"]
        )
        writer.writeheader()
        writer.writerows(rows)

    print(f"Wrote detailed results to {csv_path.resolve()}")

if __name__ == "__main__":
    main()
