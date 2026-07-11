#!/usr/bin/env python3
import os
import json
import subprocess
import sys

DEPENDENT_DIR = "dependent"
RESULT_JSON = "result.json"
CRITICAL_ALL = "critical_all"
OPT_PATH = os.environ.get("CONFD_OPT_PATH",
    os.path.join("..", "Taint_Analyzer", "llvm-project-llvmorg-14.0.0", "build", "bin", "opt"))
LIB_PATH = os.environ.get("CONFD_TEST_LIB_PATH",
    os.path.join("..", "Taint_Analyzer", "llvm-project-llvmorg-14.0.0", "build", "lib", "libTestPass.so"))
LL_FILE = os.environ.get("CONFD_LL_FILE", "mke2fs.ll")


def load_crit_candidates():
    """Load result.json and extract crit_candidate pairs for Phase 2 analysis."""
    if not os.path.exists(RESULT_JSON):
        print("Error: result.json not found. Run phase1.py first.")
        sys.exit(1)
    with open(RESULT_JSON, "r") as f:
        data = json.load(f)
    pairs = []
    for param_name, info in data.items():
        for candidate in info.get("crit_candidate", []):
            pair = (param_name, candidate)
            if pair not in pairs and (candidate, param_name) not in pairs:
                pairs.append(pair)
    return pairs


def find_common_line_file(pair):
    """Find the common line file for a parameter pair in dependent/ directory."""
    a, b = pair
    candidates = [a + b, b + a]
    for name in candidates:
        path = os.path.join(DEPENDENT_DIR, name)
        if os.path.exists(path):
            return path
    return None


def main():
    if not os.path.exists(DEPENDENT_DIR):
        print("Error: 'dependent/' directory not found. Run phase1.py first.")
        sys.exit(1)

    # Load candidate pairs from result.json crit_candidate field
    pairs = load_crit_candidates()
    print(f"Found {len(pairs)} crit_candidate pairs in {RESULT_JSON}")

    all_critical_lines = []
    processed = 0

    for a, b in pairs:
        common_file = find_common_line_file((a, b))
        if not common_file:
            print(f"  Skipping {a}/{b}: no common line file in {DEPENDENT_DIR}/")
            continue

        resolved = os.path.abspath(common_file)
        env = os.environ.copy()
        env["CONFD_COMMON_FILE"] = resolved

        print(f"  Running trace_analyzer for {a}/{b} ({os.path.basename(resolved)})")
        ret = subprocess.run([OPT_PATH, "-load", LIB_PATH,
                               "-enable-new-pm=0", "-test", LL_FILE,
                               "-o", os.devnull],
                              env=env)
        if ret.returncode != 0:
            print(f"    Warning: opt returned {ret.returncode}")

        critical_file = "critical"
        if os.path.exists(critical_file):
            with open(critical_file, "r") as cf:
                lines = cf.readlines()
                all_critical_lines.extend(lines)
                print(f"    → {len(lines)} critical line(s) extracted")
            processed += 1
        else:
            print(f"    Warning: critical file not generated")

    if not all_critical_lines:
        print("No critical lines collected. Nothing to do.")
        return

    # Write all critical lines to a single file for phase3
    with open(CRITICAL_ALL, "w") as f:
        f.writelines(all_critical_lines)
    deduped = len(set(line.strip() for line in all_critical_lines))
    print(f"Collected {len(all_critical_lines)} critical lines ({deduped} unique)")
    print(f"Processed {processed}/{len(pairs)} pairs")

    # Invoke phase3 with cumulative critical file
    print(f"Running phase3.py {RESULT_JSON} {CRITICAL_ALL}")
    subprocess.run([sys.executable, "phase3.py", RESULT_JSON, CRITICAL_ALL])


if __name__ == "__main__":
    main()
