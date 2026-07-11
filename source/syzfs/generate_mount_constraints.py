#!/usr/bin/env python3
"""
L3: generate_mount_constraints.py
Converts FilesystemExtractor output files into mount_constraints_{fsname}.json
for each filesystem.
"""
import os
import json
import sys
from collections import defaultdict

# ───────────────────────────────────────────────
# Parsers for each Analyzer.cc output file
# ───────────────────────────────────────────────

def parse_flags(filepath):
    """{fsname: {optnum: optname}}"""
    result = defaultdict(dict)
    if not os.path.exists(filepath):
        return result
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ", 2)
            if len(parts) < 3:
                continue
            fsname, optnum_str, optname = parts
            result[fsname][int(optnum_str)] = optname
    return result

def parse_ints(filepath):
    """{fsname: {optnum: (optname, radix)}}"""
    result = defaultdict(dict)
    if not os.path.exists(filepath):
        return result
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ", 3)
            if len(parts) < 4:
                continue
            fsname, optnum_str, optname, radix_str = parts
            result[fsname][int(optnum_str)] = (optname, int(radix_str))
    return result

def parse_enums(filepath):
    """{fsname: {(optnum, enum_label): {subval: subname}}}"""
    result = defaultdict(lambda: defaultdict(dict))
    if not os.path.exists(filepath):
        return result
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ", 4)
            if len(parts) < 5:
                continue
            fsname = parts[0]
            optnum = int(parts[1])
            enum_label = parts[2]
            eval_str = parts[3]
            subname = parts[4]
            # Use string keys for universal compat (f2fs hash, numeric enums)
            key = (optnum, enum_label)
            result[fsname][key][eval_str] = subname
    return result

def parse_fsoptions(filepath):
    """{fsname: {optnum: [field_entries]}}"""
    result = defaultdict(lambda: defaultdict(list))
    if not os.path.exists(filepath):
        return result
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ", 5)
            if len(parts) < 6:
                continue
            fsname, sfield, flagconst, cfgtype, optnum_str, enumnum_str = parts
            result[fsname][int(optnum_str)].append({
                "field": sfield,
                "flagconst": flagconst,
                "config_type": cfgtype,
                "enumnum": int(enumnum_str),
            })
    return result

def parse_fsoptionsonelayer(filepath):
    """{fsname: [onelayer_entries]}  raw form, resolved later"""
    result = defaultdict(list)
    if not os.path.exists(filepath):
        return result
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ", 8)
            if len(parts) < 9:
                continue
            fsname = parts[0]
            result[fsname].append({
                "src_field": parts[1], "src_flag": parts[2], "src_cfg": parts[3],
                "dst_field": parts[4], "dst_flag": parts[5], "dst_cfg": parts[6],
                "cmp_op": parts[7], "cmp_val": parts[8],
            })
    return result

def parse_fsdeps(filepath):
    """{fsname: (self_list, cross_list)}"""
    self_result = defaultdict(list)
    cross_result = defaultdict(list)
    if not os.path.exists(filepath):
        return (self_result, cross_result)
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split(" ")
            if len(parts) < 3:
                continue
            fsname = parts[0]
            deptype = parts[1]
            if deptype == "self":
                extra = parts[5:] if len(parts) > 5 else []
                self_result[fsname].append({
                    "opt_token": int(parts[2]) if parts[2].isdigit() else parts[2],
                    "opt_name": parts[3],
                    "dep_type": parts[4],
                    "extra": extra,
                })
            elif deptype == "cross":
                if len(parts) >= 9:
                    cross_result[fsname].append({
                        "opt_A": int(parts[2]) if parts[2].isdigit() else parts[2],
                        "opt_B": int(parts[3]) if parts[3].isdigit() else parts[3],
                        "opt_A_name": parts[4],
                        "opt_B_name": parts[5],
                        "relation": parts[6],
                        "src_file": parts[7],
                        "src_line": parts[8],
                    })
    return (self_result, cross_result)

# ───────────────────────────────────────────────
# Helpers
# ───────────────────────────────────────────────

def collect_all_fs(flag_params, int_params, enum_params, fsoptions_all):
    """Collect all unique filesystem names across all sources."""
    all_fs = set()
    all_fs.update(flag_params.keys())
    all_fs.update(int_params.keys())
    all_fs.update(enum_params.keys())
    all_fs.update(fsoptions_all.keys())
    all_fs.discard("raw")  # exclude onelayer raw sentinel
    return sorted(all_fs)

def resolve_onelayer_by_optnum(onelayer_raw, fsoptions_all):
    """
    Use src_field+src_flag to resolve which optnum(s) each onelayer entry
    belongs to, then create persistent-layer entries from the dst side.
    Returns {fsname: {optnum: [persistent_field_entries]}}
    """
    resolved = defaultdict(lambda: defaultdict(list))

    for fsname, entries in onelayer_raw.items():
        if fsname == "raw":
            continue
        # Build reverse lookup: (field, flagconst) → set of optnums
        rev = {}
        for optnum, flist in fsoptions_all.get(fsname, {}).items():
            for e in flist:
                key = (e["field"], e["flagconst"])
                rev.setdefault(key, set()).add(optnum)

        for entry in entries:
            # Resolve optnum from the src (parse-layer) side
            src_key = (entry["src_field"], entry["src_flag"])
            optnums = rev.get(src_key, set())
            for onum in optnums:
                resolved[fsname][onum].append({
                    "field": entry["dst_field"],
                    "flagconst": entry["dst_flag"],
                    "config_type": entry["dst_cfg"],
                    "layer": "persistent",
                })
    return resolved

OPPOSITE_PAIRS = [
    ("set", "clear"),
    ("clear", "set"),
    ("enumset", "enumclear"),
    ("enumclear", "enumset"),
    ("bitfieldset", "bitfieldclear"),
    ("bitfieldclear", "bitfieldset"),
    ("assigntrue", "assignfalse"),
    ("assignfalse", "assigntrue"),
    ("functionrettrue", "functionretfalse"),
    ("functionretfalse", "functionrettrue"),
]

def is_flag_opposition(optA, optB, fsoptions_all, fsname):
    """True if A and B toggle the same flag bit in opposite directions."""
    entriesA = fsoptions_all.get(fsname, {}).get(optA, [])
    entriesB = fsoptions_all.get(fsname, {}).get(optB, [])
    for ea in entriesA:
        for eb in entriesB:
            if ea["field"] != eb["field"]:
                continue
            fc_a, fc_b = ea["flagconst"], eb["flagconst"]
            # Sentinel flags (0xfffffff0 / 0xfffffff1, or decimal 4294967280/4294967281)
            # only differ in LSB; use relaxed match so opposite pairs like
            # assigntrue↔assignfalse and functionrettrue↔functionretfalse can be filtered.
            try:
                ia = int(fc_a, 0)
                ib = int(fc_b, 0)
                if ia in (0xfffffff0, 0xfffffff1) and ib in (0xfffffff0, 0xfffffff1):
                    flag_match = (ia | 1) == (ib | 1)
                else:
                    flag_match = (fc_a == fc_b)
            except ValueError:
                flag_match = (fc_a == fc_b)
            if flag_match and (ea["config_type"], eb["config_type"]) in OPPOSITE_PAIRS:
                return True
    return False

HARD_RELATIONS = {
    "must_be_smaller", "must_be_greater",
    "mutual_exclusion",
    "requires_enable", "requires_disable",
}
SILENT_RELATIONS = {"silent_clear", "silent_enable"}

REL_NORMALIZE = {
    "must_be_smaller": "smaller",
    "must_be_greater": "greater",
    "requires_enable": "enable",
    "requires_disable": "disable",
}

def build_cross_deps(fsname, cross_deps, fsoptions_all):
    """From cross_deps[fsname] build (dep, critical, silent) mappings."""
    dep = defaultdict(set)
    critical = defaultdict(dict)
    silent = defaultdict(set)

    for cd in cross_deps.get(fsname, []):
        A = cd["opt_A"]
        B = cd["opt_B"]
        rel = cd["relation"]
        if A == B:
            continue
        if is_flag_opposition(A, B, fsoptions_all, fsname):
            continue

        if rel in HARD_RELATIONS:
            dep[A].add(B)
            dep[B].add(A)
            norm = REL_NORMALIZE.get(rel, rel)
            if rel == "mutual_exclusion":
                critical[A][B] = norm
                critical[B][A] = norm
            else:
                critical[A][B] = norm
        elif rel in SILENT_RELATIONS:
            silent[A].add(B)
            silent[B].add(A)

    return dep, critical, silent

# ───────────────────────────────────────────────
# Main builder
# ───────────────────────────────────────────────

def fsname_name_lookup(fsname, optnum, flag_params, int_params, enum_params):
    """Get the human-readable name for an option by its optnum in fsname."""
    # Check flags
    if optnum in flag_params.get(fsname, {}):
        return flag_params[fsname][optnum]
    # Check ints
    if optnum in int_params.get(fsname, {}):
        return int_params[fsname][optnum][0]
    # Check enums
    for (eonum, elabel), _ in enum_params.get(fsname, {}).items():
        if eonum == optnum:
            return elabel
    return str(optnum)

def build_mount_constraints(fsname, flag_params, int_params, enum_params,
                            fsoptions_all, onelayer_resolved,
                            cross_deps, self_deps):
    """Build the full mount_constraints dict for one filesystem."""
    # --- Step 1: merge parameter lists ---
    all_params = {}  # optnum → {"name", "type", [radix]}
    for onum, name in flag_params.get(fsname, {}).items():
        all_params[onum] = {"name": name, "type": "flag"}
    for onum, (name, radix) in int_params.get(fsname, {}).items():
        all_params[onum] = {"name": name, "type": "int", "radix": radix}
    for (onum, elabel), subvals in enum_params.get(fsname, {}).items():
        if onum not in all_params:
            all_params[onum] = {"name": elabel, "type": "enum"}
        else:
            # An option already known as flag may also have enum sub-values
            all_params[onum]["type"] = "enum"
            all_params[onum]["enum_subvals"] = subvals
    for onum in fsoptions_all.get(fsname, {}):
        if onum not in all_params:
            all_params[onum] = {"name": str(onum), "type": "flag"}

    if not all_params:
        return {}

    sorted_params = sorted(all_params.items())
    optnum_to_id = {}
    for idx, (onum, _) in enumerate(sorted_params, 1):
        optnum_to_id[onum] = idx

    # --- Step 2: build cross dependencies ---
    dep_map, critical_map, silent_map = build_cross_deps(
        fsname, cross_deps, fsoptions_all)

    # --- Step 3: assemble entries ---
    constraints = {}
    for onum, pinfo in sorted_params:
        name = pinfo["name"]
        entry = {
            "id": optnum_to_id[onum],
            "takes_value": {"flag": "no", "int": "yes", "enum": "enum"}[pinfo["type"]],
            "dependency": [],
            "critical": {},
            "silent_dep": [],
            "all_fields": [],
        }
        if pinfo["type"] == "int" and "radix" in pinfo:
            entry["radix"] = pinfo["radix"]

        # --- Dependency / critical / silent ---
        dset = dep_map.get(onum, set())
        entry["dependency"] = sorted(
            fsname_name_lookup(fsname, d, flag_params, int_params, enum_params)
            for d in dset if d in all_params)

        crit = critical_map.get(onum, {})
        entry["critical"] = {
            fsname_name_lookup(fsname, k, flag_params, int_params, enum_params): v
            for k, v in crit.items() if k in all_params
        }

        sset = silent_map.get(onum, set())
        entry["silent_dep"] = sorted(
            fsname_name_lookup(fsname, s, flag_params, int_params, enum_params)
            for s in sset if s in all_params)

        # --- Self constraints ---
        for sd in self_deps.get(fsname, []):
            if sd["opt_token"] == onum:
                if sd["dep_type"] == "range" and len(sd["extra"]) >= 2:
                    entry["value_range_min"] = sd["extra"][0]
                    entry["value_range_max"] = sd["extra"][1]
                elif sd["dep_type"] == "discrete":
                    if len(sd["extra"]) > 1:
                        entry["discrete_values"] = sd["extra"][1:]  # skip count header

        # --- Enum values ---
        for (eonum, elabel), subvals in enum_params.get(fsname, {}).items():
            if eonum == onum:
                entry["enum_values"] = {}
                for k, v in subvals.items():
                    entry["enum_values"][str(k)] = v

        # --- All fields from fsoptions (primary) ---
        seen = set()
        for fe in fsoptions_all.get(fsname, {}).get(onum, []):
            fid = (fe["field"], fe["flagconst"], fe["config_type"])
            if fid not in seen:
                seen.add(fid)
                entry["all_fields"].append({
                    "field": fe["field"],
                    "flagconst": fe["flagconst"],
                    "config_type": fe["config_type"],
                    "layer": "parse",
                })

        # --- All fields from onelayer (persistent layer) ---
        for fe in onelayer_resolved.get(fsname, {}).get(onum, []):
            fid = (fe["field"], fe["flagconst"], fe["config_type"])
            if fid not in seen:
                seen.add(fid)
                entry["all_fields"].append(fe)

        constraints[name] = entry

    return constraints

# ───────────────────────────────────────────────
# Entry point
# ───────────────────────────────────────────────

def main():
    workdir = os.getcwd()
    files = {
        "fsflags": os.path.join(workdir, "fsflags"),
        "fsints": os.path.join(workdir, "fsints"),
        "fsenums": os.path.join(workdir, "fsenums"),
        "fsoptions": os.path.join(workdir, "fsoptions"),
        "fsoptionsonelayer": os.path.join(workdir, "fsoptionsonelayer"),
        "fsdeps": os.path.join(workdir, "fsdeps"),
    }

    print("[L3] Parsing input files...")
    flag_params = parse_flags(files["fsflags"])
    int_params = parse_ints(files["fsints"])
    enum_params = parse_enums(files["fsenums"])
    fsoptions_all = parse_fsoptions(files["fsoptions"])
    onelayer_raw = parse_fsoptionsonelayer(files["fsoptionsonelayer"])
    self_deps, cross_deps = parse_fsdeps(files["fsdeps"])

    all_fs = collect_all_fs(flag_params, int_params, enum_params, fsoptions_all)
    if not all_fs:
        print("[L3] No filesystem data found. Run FilesystemExtractor first.")
        sys.exit(1)
    print(f"[L3] Filesystems: {all_fs}")

    onelayer_resolved = resolve_onelayer_by_optnum(onelayer_raw, fsoptions_all)

    for fsname in all_fs:
        print(f"[L3] Building constraints for {fsname}...")
        constraints = build_mount_constraints(
            fsname, flag_params, int_params, enum_params,
            fsoptions_all, onelayer_resolved,
            cross_deps, self_deps)

        out_path = os.path.join(workdir, f"mount_constraints_{fsname}.json")
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(constraints, f, indent=2, ensure_ascii=False)
        print(f"  -> {out_path}  ({len(constraints)} params)")

if __name__ == "__main__":
    main()
