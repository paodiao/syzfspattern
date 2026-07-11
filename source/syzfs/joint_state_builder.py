#!/usr/bin/env python3
"""
L6: joint_state_builder.py

Generates paired (mkfs command, mount command) for a given caseIdx, satisfying
path constraints from Analyzer.cc, option-level constraints from the constraint
JSONs, and cross-component compatibility from cross_dependency.

Usage:
    python joint_state_builder.py <caseIdx> <max_depth> <max_states> [opts_dir]

    caseIdx    — case index matching mkfs_opts_{n}.txt / mount_opts_{n}.txt
    max_depth  — DFS max depth (applied independently to mkfs and mount)
    max_states — DFS max states (applied independently to mkfs and mount)
    opts_dir   — directory containing all input files (default: cwd)

Input (6 files, auto-resolved from caseIdx and filesystem name):
    mkfs_opts_{n}.txt              — mkfs path constraints
    mount_opts_{n}.txt             — mount path constraints
    {mkfs_constraints}.json        — mkfs option definitions
    mount_constraints_{fs}.json    — mount option definitions
    superblock_mapping_{fs}.json   — formula inverse transform
    cross_dependency_{n}.json      — cross-component compatibility

Output:
    joint_states_{n}.txt           — paired command lines
"""

import copy
import json
import os
import re
import sys
from collections import defaultdict

# Hardcoded paths
DEVICE = "/dev/sda1"
MOUNT_POINT = "/mnt"
IMG_FILE = "/tmp/img"

# ──────────────────────────────────────────────────
# Regex patterns (same as cross_dependency.py)
# ──────────────────────────────────────────────────
_FLAG_RE = re.compile(r'^(no)?([a-zA-Z0-9_]\w*)$')
_CONSTRAINT_RE = re.compile(r'(>=|<=|!=|>|<|=)(-?\d+)$')

# ──────────────────────────────────────────────────
# File naming
# ──────────────────────────────────────────────────

def mkfs_constraints_fname(fsname):
    if fsname == 'ext4':
        return 'mke2fs_constraints.json'
    if fsname == 'ntfs3':
        return 'mkntfs3_constraints.json'
    return f'mkfs_{fsname}_constraints.json'


def mount_constraints_fname(fsname):
    return f'mount_constraints_{fsname}.json'


def superblock_mapping_fname(fsname):
    return f'superblock_mapping_{fsname}.json'


# ──────────────────────────────────────────────────
# Path-constraint parsing
# ──────────────────────────────────────────────────

def parse_constraint_line(line):
    """Return (name, op, val, is_flag, is_negated) or None."""
    mf = _FLAG_RE.match(line)
    if mf:
        neg = mf.group(1) is not None
        name = mf.group(2)
        return (name, None, None, True, neg)

    m = _CONSTRAINT_RE.search(line)
    if m:
        op = m.group(1)
        try:
            val = int(m.group(2))
        except ValueError:
            return None
        name = line[:m.start()]
        return (name, op, val, False, False)

    return None


def parse_opts_file(path):
    """Return (fs_name, [group_lines])."""
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    content = content.replace('\r\n', '\n').replace('\r', '\n')
    parts = content.split('---\n')
    fs_name = parts[0].strip()
    groups = []
    for p in parts[1:]:
        lines = [ln.strip() for ln in p.split('\n') if ln.strip()]
        groups.append(lines)
    return fs_name, groups


def parse_path_constraints(lines):
    """
    Parse a single group's lines into (locked, bounds).
    locked = {name: "enable"/"disable"/val}
    bounds = {name: [(op, val)]}
    """
    locked = {}
    bounds = defaultdict(list)
    for line in lines:
        parsed = parse_constraint_line(line)
        if parsed is None:
            continue
        name, op, val, is_flag, neg = parsed
        if is_flag:
            locked[name] = "disable" if neg else "enable"
        elif op == '=':
            locked[name] = val
        else:
            bounds[name].append((op, val))
    return locked, dict(bounds)


# ──────────────────────────────────────────────────
# Inverse transform (formula-based)
# ──────────────────────────────────────────────────

def load_inverse_lookup(sm_path):
    """Return {confd_param: (inv_type, const)} from superblock_mapping."""
    with open(sm_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    lookup = {}
    for entry in data.get('confd_to_superblock', []):
        param = entry.get('confd_param', '')
        if not param:
            continue
        transform = entry.get('transform', '')
        formula = entry.get('formula', '')
        inv_type, const = _parse_formula(formula, transform)
        lookup[param] = (inv_type, const)
    return lookup


def _parse_formula(formula, transform):
    """Same logic as inverse_transform.parse_formula."""
    if transform in ('conditional', 'conditional_rev', 'computed',
                     'bitmask_check'):
        return ('skip', None)
    if not formula:
        if transform == 'direct':
            return ('direct', 1)
        if transform == 'log2_scale':
            return ('log2_pure', 1)
        return ('skip', None)
    fm = formula.strip()
    m = re.search(r'log2\(\s*user_value\s*/\s*(\d+)', fm)
    if m:
        return ('log2_div', int(m.group(1)))
    m = re.search(r'log2\(\s*user_value\s*/\s*(sector_size|block_size|cluster_size)', fm)
    if m:
        return ('log2_dep', None)
    if re.search(r'log2\(\s*user_value\s*\)', fm):
        return ('log2_pure', 1)
    if re.search(r':= user_value\b', fm):
        return ('direct', 1)
    if transform == 'direct':
        return ('direct', 1)
    if transform == 'log2_scale':
        return ('log2_pure', 1)
    return ('skip', None)


def inverse_value(cmpval, inv_type, const):
    if inv_type == 'direct':
        return cmpval
    if inv_type == 'log2_pure':
        return 1 << cmpval
    if inv_type == 'log2_div':
        return const * (1 << cmpval)
    return None


def transform_mkfs_config(locked, bounds, inv_lookup):
    """
    Apply inverse_transform to mkfs-side constraint values.
    Returns (transformed_locked, transformed_bounds).
    """
    tlocked = {}
    for name, val in locked.items():
        if isinstance(val, int) and name in inv_lookup:
            itype, const = inv_lookup[name]
            nv = inverse_value(val, itype, const)
            tlocked[name] = nv if nv is not None else val
        else:
            tlocked[name] = val

    tbounds = defaultdict(list)
    for name, entries in bounds.items():
        for op, val in entries:
            if name in inv_lookup:
                itype, const = inv_lookup[name]
                nv = inverse_value(val, itype, const)
                tbounds[name].append((op, nv if nv is not None else val))
            else:
                tbounds[name].append((op, val))
    return tlocked, dict(tbounds)


# ──────────────────────────────────────────────────
# Apply path bounds to constraint_data value_range
# ──────────────────────────────────────────────────

def apply_path_bounds(constraint_data, bounds):
    """Narrow value_range_min/max according to inequality path constraints."""
    adjusted = copy.deepcopy(constraint_data)
    for name, entries in bounds.items():
        e = adjusted.setdefault(name, {})
        for op, val in entries:
            if op == '<':
                cur = e.get('value_range_max')
                new = str(val - 1)
                if cur is None or int(new) < int(cur):
                    e['value_range_max'] = new
            elif op == '<=':
                cur = e.get('value_range_max')
                new = str(val)
                if cur is None or int(new) < int(cur):
                    e['value_range_max'] = new
            elif op == '>':
                cur = e.get('value_range_min')
                new = str(val + 1)
                if cur is None or int(new) > int(cur):
                    e['value_range_min'] = new
            elif op == '>=':
                cur = e.get('value_range_min')
                new = str(val)
                if cur is None or int(new) > int(cur):
                    e['value_range_min'] = new
    return adjusted


# ──────────────────────────────────────────────────
# DFS helpers
# ──────────────────────────────────────────────────

def int_candidates(entry, exclude=None):
    vals = []
    vmin = entry.get("value_range_min")
    vmax = entry.get("value_range_max")
    if vmin is not None:
        vals.append(vmin)
    if vmax is not None:
        vals.append(vmax)
    if vmin is not None and vmax is not None:
        mid = str((int(vmin) + int(vmax)) // 2)
        if mid not in vals:
            vals.append(mid)
    if not vals:
        vals.append("1")
    if exclude is not None:
        vals = [v for v in vals if v != exclude]
    return vals


def enum_candidates(entry, exclude=None):
    ev = entry.get("enum_values", {})
    vals = list(ev.values())
    if exclude is not None:
        vals = [v for v in vals if v != exclude]
    return vals


def build_next_list(entry, constraint_data):
    ids = []
    for dep in entry.get("dependency", []):
        if dep in constraint_data:
            ids.append(constraint_data[dep]["id"])
    for other in entry.get("critical", {}):
        if other in constraint_data:
            ids.append(constraint_data[other]["id"])
    for sentry in entry.get("silent_dep", []):
        target = sentry.split(":")[0] if ":" in sentry else sentry
        if target in constraint_data:
            ids.append(constraint_data[target]["id"])
    return ids


def verify_config(config, constraint_data):
    for name, val in config.items():
        entry = constraint_data.get(name, {})
        tv = entry.get("takes_value", "no")

        if tv in ("yes", "flag_only"):
            vmin = entry.get("value_range_min")
            vmax = entry.get("value_range_max")
            try:
                iv = int(val)
            except (ValueError, TypeError):
                continue
            if vmax is not None and iv > int(vmax):
                return False
            if vmin is not None and iv < int(vmin):
                return False

        if tv == "enum":
            ev = entry.get("enum_values", {})
            if ev and val not in ev.values():
                return False

        for other, rel in entry.get("critical", {}).items():
            ov = config.get(other)
            if rel == "enable" and (ov is None or ov == "disable"):
                return False
            if rel == "disable" and ov == "enable":
                return False
            if rel == "mutual_exclusion" and val == "enable" and ov == "enable":
                return False
            if rel == "smaller" and ov is not None:
                try:
                    if int(val) < int(ov):
                        return False
                except (ValueError, TypeError):
                    pass
            if rel == "greater" and ov is not None:
                try:
                    if int(val) > int(ov):
                        return False
                except (ValueError, TypeError):
                    pass
    return True


# ──────────────────────────────────────────────────
# DFS Generator
# ──────────────────────────────────────────────────

def generate(config, constraint_data, target_num, final_states,
             try_list, locked_set, id_to_name,
             max_depth, depth, states_made):
    depth += 1
    for id_val in try_list:
        name = id_to_name.get(id_val)
        if name is None:
            continue
        if states_made[0] >= target_num or depth > max_depth:
            break

        entry = constraint_data.get(name, {})
        if not entry:
            continue

        locked = name in locked_set
        existing = config.get(name)

        # ── locked item: only propagate deps ──
        if locked and existing is not None:
            next_ids = build_next_list(entry, constraint_data)
            if next_ids:
                generate(config, constraint_data, target_num, final_states,
                         next_ids, locked_set, id_to_name,
                         max_depth, depth, states_made)
            continue

        # Skip locked items that somehow have no value
        if locked:
            continue

        # ── normal exploration ──
        new_cfgs = []
        tv = entry.get("takes_value", "no")

        if existing is not None:
            if tv == "no":
                nv = "disable" if existing == "enable" else "enable"
                new_cfgs.append({**config, name: nv})
            elif tv == "yes":
                for v in int_candidates(entry, existing):
                    new_cfgs.append({**config, name: v})
            elif tv == "enum":
                for v in enum_candidates(entry, existing):
                    new_cfgs.append({**config, name: v})
        else:
            if tv == "no":
                new_cfgs.append({**config, name: "enable"})
            elif tv == "yes":
                for v in int_candidates(entry):
                    new_cfgs.append({**config, name: v})
            elif tv == "enum":
                for v in enum_candidates(entry):
                    new_cfgs.append({**config, name: v})

        for cfg in new_cfgs:
            if cfg in final_states:
                continue
            if depth > 0 and verify_config(cfg, constraint_data):
                states_made[0] += 1
                final_states.append(cfg)
                next_ids = build_next_list(entry, constraint_data)
                if next_ids:
                    generate(cfg, constraint_data, target_num, final_states,
                             next_ids, locked_set, id_to_name,
                             max_depth, depth, states_made)

    # No depth decrement needed (local scope)


# ──────────────────────────────────────────────────
# Command formatters
# ──────────────────────────────────────────────────

def ConfigToMkfsCMD(config, constraint_data, fsname="ext4",
                    device=DEVICE, img=IMG_FILE):
    tool = {"ext4": "mke2fs", "xfs": "mkfs.xfs", "btrfs": "mkfs.btrfs",
            "f2fs": "mkfs.f2fs", "erofs": "mkfs.erofs", "exfat": "mkfs.exfat",
            "ntfs3": "mkntfs"}.get(fsname, "mke2fs")
    output = f"({tool}) {tool}"
    groups = {}

    for arg, val in config.items():
        entry = constraint_data.get(arg, {})
        flag = entry.get("flag", "")
        tv = entry.get("takes_value", "no")
        if not flag:
            continue

        parts = flag.split(" ", 1)
        base = parts[0]
        key = parts[1] if len(parts) > 1 else ""

        groups.setdefault(base, [])

        if tv == "no":
            groups[base].append(f"^{arg}" if val == "disable" else arg)
        elif tv == "flag_only":
            output += " " + base
            continue
        else:
            frag = f"{key}={val}" if key else str(val)
            groups[base].append(frag)

    for base, items in groups.items():
        output += " " + base + " " + ",".join(items)

    target = img if tool == "mke2fs" else device
    output += " " + target
    return output


def ConfigToMountCMD(config, constraint_data, fsname="ext4",
                     device=DEVICE, target=MOUNT_POINT):
    opts = []
    for name, val in config.items():
        entry = constraint_data.get(name, {})
        tv = entry.get("takes_value", "no")
        if tv == "no":
            opts.append("no" + name if val == "disable" else name)
        elif tv in ("yes", "enum"):
            opts.append(f"{name}={val}")

    opt_str = ",".join(opts) if opts else "defaults"
    return f"(mount) mount -t {fsname} -o {opt_str} {device} {target}"


# ──────────────────────────────────────────────────
# Cross-component filter
# ──────────────────────────────────────────────────

def cross_compatible(mkfs_cfg, mount_cfg, cross_dep_data, group_idx=0):
    """
    Check whether a mkfs config and mount config are compatible
    according to cross_dependency.json for the specified group.
    """
    groups = cross_dep_data.get("groups", [])
    if not groups or group_idx >= len(groups):
        return True
    grp = groups[group_idx]


    conflicts = grp.get("conflicts", [])
    if not conflicts:
        return True

    for c in conflicts:
        ctype = c.get("type", "")
        name = c.get("name", "")

        if ctype == "flag_mismatch":
            mkfs_val = mkfs_cfg.get(name)
            mount_val = mount_cfg.get(name)
            m_mkfs = c.get("mkfs", "")
            m_mount = c.get("mount", "")

            mkfs_match = ((m_mkfs == "enable" and mkfs_val == "enable") or
                          (m_mkfs == "disable" and mkfs_val == "disable"))
            mount_match = ((m_mount == "enable" and mount_val == "enable") or
                           (m_mount == "disable" and mount_val == "disable"))
            if mkfs_match and mount_match:
                return False

        if ctype == "value_range_empty":
            return False

    return True


# ──────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────

def main():
    if len(sys.argv) < 4:
        print("Usage: python joint_state_builder.py <caseIdx> <max_depth> "
              "<max_states> [opts_dir]")
        sys.exit(1)

    case_idx = sys.argv[1]
    max_depth = int(sys.argv[2])
    max_states = int(sys.argv[3])
    opts_dir = sys.argv[4] if len(sys.argv) > 4 else os.getcwd()

    # ── Resolve input files ──
    mkfs_path = os.path.join(opts_dir, f"mkfs_opts_{case_idx}.txt")
    mount_path = os.path.join(opts_dir, f"mount_opts_{case_idx}.txt")
    cross_path = os.path.join(opts_dir, f"cross_dependency_{case_idx}.json")

    if not os.path.exists(mkfs_path):
        print(f"Missing: {mkfs_path}")
        sys.exit(1)
    if not os.path.exists(mount_path):
        print(f"Missing: {mount_path}")
        sys.exit(1)

    # ── Parse path constraints ──
    mkfs_fs, mkfs_groups = parse_opts_file(mkfs_path)
    mount_fs, mount_groups = parse_opts_file(mount_path)

    if mkfs_fs != mount_fs:
        print(f"FS mismatch: {mkfs_fs} vs {mount_fs}")
        sys.exit(1)

    fsname = mkfs_fs
    print(f"[L6] Filesystem: {fsname}, caseIdx={case_idx}")

    n_groups = min(len(mkfs_groups), len(mount_groups))
    if len(mkfs_groups) != len(mount_groups):
        print(f"[L6] warn: group count mismatch mkfs={len(mkfs_groups)} "
              f"mount={len(mount_groups)}, using first {n_groups}")

    # ── Load constraint JSONs ──
    mkfs_cfile = mkfs_constraints_fname(fsname)
    mount_cfile = mount_constraints_fname(fsname)
    sm_file = superblock_mapping_fname(fsname)

    for fname in [mkfs_cfile, mount_cfile]:
        fpath = os.path.join(opts_dir, fname)
        if not os.path.exists(fpath):
            print(f"Missing: {fpath}")
            sys.exit(1)

    with open(os.path.join(opts_dir, mkfs_cfile), encoding='utf-8') as f:
        mkfs_raw = json.load(f)
    mkfs_constraints = mkfs_raw.get("parameters", mkfs_raw)

    with open(os.path.join(opts_dir, mount_cfile), encoding='utf-8') as f:
        mount_constraints = json.load(f)

    # ── Inverse transform lookup (per-FS, not per-group) ──
    sm_path = os.path.join(opts_dir, sm_file)
    inv_lookup = load_inverse_lookup(sm_path) if os.path.exists(sm_path) else {}

    # ── Build lookup tables (per-FS) ──
    mkfs_id_to_name = {e["id"]: n for n, e in mkfs_constraints.items()}
    mkfs_all_ids = sorted(e["id"] for e in mkfs_constraints.values())

    mount_id_to_name = {e["id"]: n for n, e in mount_constraints.items()}
    mount_all_ids = sorted(e["id"] for e in mount_constraints.values())

    # ── Load cross_dependency ──
    cross_data = {}
    if os.path.exists(cross_path):
        with open(cross_path, encoding='utf-8') as f:
            cross_data = json.load(f)

    out_name = f"joint_states_{case_idx}.txt"
    out_path = os.path.join(opts_dir, out_name)
    total_written = 0

    with open(out_path, "w", encoding="utf-8") as out:
        for gi in range(n_groups):
            print(f"[L6] Processing group {gi}/{n_groups}")
            mkfs_locked, mkfs_bounds = parse_path_constraints(
                mkfs_groups[gi] if gi < len(mkfs_groups) else [])
            mount_locked, mount_bounds = parse_path_constraints(
                mount_groups[gi] if gi < len(mount_groups) else [])

            # ── Inverse transform mkfs values ──
            mkfs_locked, mkfs_bounds = transform_mkfs_config(
                mkfs_locked, mkfs_bounds, inv_lookup)

            # ── Apply path bounds (per-group, fresh copy) ──
            mkfs_cd = apply_path_bounds(mkfs_constraints, mkfs_bounds)
            mount_cd = apply_path_bounds(mount_constraints, mount_bounds)

            # ── Pre-populate locked values ──
            mkfs_start_cfg = dict(mkfs_locked)
            mount_start_cfg = dict(mount_locked)

            # ── Phase 1a: expand mkfs ──
            mkfs_configs = []
            generate(mkfs_start_cfg, mkfs_cd, max_states, mkfs_configs,
                     mkfs_all_ids, set(mkfs_locked), mkfs_id_to_name,
                     max_depth, 0, [0])
            print(f"      -> {len(mkfs_configs)} mkfs configs")

            # ── Phase 1b: expand mount ──
            mount_configs = []
            generate(mount_start_cfg, mount_cd, max_states, mount_configs,
                     mount_all_ids, set(mount_locked), mount_id_to_name,
                     max_depth, 0, [0])
            print(f"      -> {len(mount_configs)} mount configs")

            # ── Phase 2: cross + pair ──
            group_joint = []
            for mc in mkfs_configs:
                for mtc in mount_configs:
                    if cross_compatible(mc, mtc, cross_data, gi):
                        group_joint.append((mc, mtc))

            print(f"  group {gi} joint states: {len(group_joint)} (of "
                  f"{len(mkfs_configs)}x{len(mount_configs)} pairs)")

            # ── Phase 3: output ──
            for mc, mtc in group_joint:
                mline = ConfigToMkfsCMD(mc, mkfs_cd, fsname)
                cline = ConfigToMountCMD(mtc, mount_cd, fsname)
                out.write(mline + "\n")
                out.write(cline + "\n")
                total_written += 1

    print(f"[L6] Written {total_written} joint states -> {out_name}")


if __name__ == "__main__":
    main()
