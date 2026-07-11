#!/usr/bin/env python3
"""
cross_dependency.py

Combines per-group mkfs and mount constraints from Analyzer.cc output into
a unified cross-component dependency JSON.  Each group comes from the same
kernel control path — they are co-necessary — so compatibility analysis is
performed directly within each aligned group.

Usage:
    python cross_dependency.py [opts_dir]

    opts_dir: directory containing mount_opts_*.txt and
              mkfs_opts_*.txt (default: cwd)

Output:
    cross_dependency_{n}.json — per-caseIdx cross-component dependency
"""

import re
import json
import sys
import os
import glob
from collections import defaultdict


# ---------------------------------------------------------------------------
# Regex: flag line
# ---------------------------------------------------------------------------
# Matches "64bit" or "no64bit" (flag-only, no operator + value)
_FLAG_RE = re.compile(r'^(no)?([a-zA-Z0-9_]\w*)$')


# Regex: constraint line  (name + op + value)
# Matches "blocksize<12"  "inodesize>=256"  "encoding=3"  "data=ordered"
_CONSTRAINT_RE = re.compile(
    r'(>=|<=|!=|>|<|=)(-?\d+|\S+)$'
)


# ---------------------------------------------------------------------------
# File parsing
# ---------------------------------------------------------------------------

def parse_opts_file(path):
    """
    Return (fs_name, [group_lines]).

    Each group_lines is a list of non-empty strings (one per constraint line).
    Empty groups become [].
    """
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Normalise line endings
    content = content.replace('\r\n', '\n').replace('\r', '\n')

    # Split on "---\n" —  first segment is the header
    parts = content.split('---\n')
    fs_name = parts[0].strip()

    groups = []
    for p in parts[1:]:
        lines = [ln.strip() for ln in p.split('\n') if ln.strip()]
        groups.append(lines)

    return fs_name, groups


def parse_constraint_line(line):
    """
    Return (name, op, value, is_flag, is_negated)

    Flags:   "64bit"                → ('64bit', None, None, True, False)
             "noinline_data"        → ('inline_data', None, None, True, True)
    Values:  "blocksize<12"         → ('blocksize', '<',  12, False, False)
             "inodesize>=256"       → ('inodesize', '>=', 256, False, False)
    """
    # Try flag first
    mf = _FLAG_RE.match(line)
    if mf:
        neg = mf.group(1) is not None
        name = mf.group(2)
        return (name, None, None, True, neg)

    # Try value constraint
    m = _CONSTRAINT_RE.search(line)
    if m:
        op = m.group(1)
        val_str = m.group(2)
        try:
            val = int(val_str)
        except ValueError:
            val = val_str  # keep as string for enum values like "ordered"
        name = line[:m.start()]
        return (name, op, val, False, False)

    return None


def build_group_dict(lines):
    """
    Return (flags, values) where:
        flags  = {name: {'negated': bool}}
        values = {name: [(op, val)]}   # list in case of duplicate (rare)
    """
    flags = {}
    values = defaultdict(list)
    for line in lines:
        parsed = parse_constraint_line(line)
        if parsed is None:
            continue
        name, op, val, is_flag, neg = parsed
        if is_flag:
            flags[name] = {'negated': neg}
        else:
            values[name].append((op, val))
    return dict(flags), dict(values)


# ---------------------------------------------------------------------------
# Value interval representation
# ---------------------------------------------------------------------------

def to_interval(op, val):
    """
    Convert constraint (op, val) to an interval (lo, hi, lo_open, hi_open).

    lo_open=True  → open at lo  (lo < x)
    hi_open=True  → open at hi  (x < hi)

    Returns None for != (not expressible as a simple interval).
    """
    if isinstance(val, str):
        # non-numeric (enum value): only = makes sense as a point
        if op == '=':
            return (val, val, False, False)
        return None
    if op == '=':
        return (val, val, False, False)
    if op == '>':
        return (val, float('inf'), True, False)
    if op == '>=':
        return (val, float('inf'), False, False)
    if op == '<':
        return (float('-inf'), val, False, True)
    if op == '<=':
        return (float('-inf'), val, False, False)
    if op == '!=':
        return None
    return None


def intervals_intersect(a, b):
    """
    Two intervals intersect iff  max(lo_a, lo_b) < min(hi_a, hi_b),
    with appropriate handling of open/closed boundaries.
    """
    lo_a, hi_a, lo_open_a, hi_open_a = a
    lo_b, hi_b, lo_open_b, hi_open_b = b

    lo = max(lo_a, lo_b)
    hi = min(hi_a, hi_b)

    lo_open = (lo_open_a if lo == lo_a else lo_open_b) if lo_a != lo_b else (lo_open_a or lo_open_b)
    hi_open = (hi_open_a if hi == hi_a else hi_open_b) if hi_a != hi_b else (hi_open_a or hi_open_b)

    if lo < hi:
        return True
    if lo > hi:
        return False
    # lo == hi
    if lo_open or hi_open:
        return False  # (a, a) → empty
    return True        # [a, a] → single point, non-empty


def value_list_intersects(mkfs_vals, mount_vals):
    """
    Check if ANY pair of (mkfs_ival, mount_ival) intersects.
    For != we skip interval and treat as compatible (can't represent).
    """
    mkfs_ivals = []
    for op, v in mkfs_vals:
        iv = to_interval(op, v)
        if iv is None:
            return True  # != → conservative: compatible
        mkfs_ivals.append(iv)

    mount_ivals = []
    for op, v in mount_vals:
        iv = to_interval(op, v)
        if iv is None:
            return True
        mount_ivals.append(iv)

    for a in mkfs_ivals:
        for b in mount_ivals:
            if intervals_intersect(a, b):
                return True
    return False


# ---------------------------------------------------------------------------
# Group-level analysis
# ---------------------------------------------------------------------------

def analyze_group(mkfs_flags, mkfs_values, mount_flags, mount_values):
    """
    Compare constraints within a single aligned group.

    Returns a dict ready for JSON:
    {
      "compatible": bool,
      "mutual": {
        "flags": [{name, mkfs, mount, compatible}],
        "values": [{name, mkfs_op, mkfs_val, mount_op, mount_val, compatible}]
      },
      "mkfs_only": {"flags": [...], "values": {name: [(op,val)]}},
      "mount_only": {"flags": [...], "values": {name: [(op,val)]}},
      "conflicts": [...]
    }
    """
    mutual_flags = []
    mutual_values = []
    conflicts = []

    all_names = set(mkfs_flags.keys()) | set(mkfs_values.keys()) | \
                set(mount_flags.keys()) | set(mount_values.keys())

    mkfs_only = {'flags': [], 'values': {}}
    mount_only = {'flags': [], 'values': {}}

    for name in sorted(all_names):
        in_mkfs_flag = name in mkfs_flags
        in_mount_flag = name in mount_flags
        in_mkfs_val = name in mkfs_values
        in_mount_val = name in mount_values

        mkfs_present = in_mkfs_flag or in_mkfs_val
        mount_present = in_mount_flag or in_mount_val

        # ---- mutual flag ----
        if in_mkfs_flag and in_mount_flag:
            mkfs_neg = mkfs_flags[name]['negated']
            mount_neg = mount_flags[name]['negated']
            compat = (mkfs_neg == mount_neg)
            mutual_flags.append({
                'name': name,
                'mkfs': 'disable' if mkfs_neg else 'enable',
                'mount': 'disable' if mount_neg else 'enable',
                'compatible': compat
            })
            if not compat:
                conflicts.append({
                    'type': 'flag_mismatch',
                    'name': name,
                    'mkfs': 'disable' if mkfs_neg else 'enable',
                    'mount': 'disable' if mount_neg else 'enable'
                })
            continue

        # ---- mutual value (same name) ----
        if in_mkfs_val and in_mount_val:
            compat = value_list_intersects(mkfs_values[name], mount_values[name])
            mutual_values.append({
                'name': name,
                'mkfs': [f'{op}{v}' for op, v in mkfs_values[name]],
                'mount': [f'{op}{v}' for op, v in mount_values[name]],
                'compatible': compat
            })
            if not compat:
                conflicts.append({
                    'type': 'value_range_empty',
                    'name': name,
                    'mkfs': [f'{op}{v}' for op, v in mkfs_values[name]],
                    'mount': [f'{op}{v}' for op, v in mount_values[name]]
                })
            continue

        # ---- flag vs value mismatch (same name, different kind) ----
        if in_mkfs_flag and in_mount_val:
            conflicts.append({
                'type': 'kind_mismatch',
                'name': name,
                'mkfs': 'flag',
                'mount': 'value'
            })
            continue
        if in_mkfs_val and in_mount_flag:
            conflicts.append({
                'type': 'kind_mismatch',
                'name': name,
                'mkfs': 'value',
                'mount': 'flag'
            })
            continue

        # ---- one-sided ----
        if mkfs_present and not mount_present:
            if in_mkfs_flag:
                mkfs_only['flags'].append({
                    'name': name, 'negated': mkfs_flags[name]['negated']
                })
            else:
                mkfs_only['values'][name] = [f'{op}{v}' for op, v in mkfs_values[name]]

        if mount_present and not mkfs_present:
            if in_mount_flag:
                mount_only['flags'].append({
                    'name': name, 'negated': mount_flags[name]['negated']
                })
            else:
                mount_only['values'][name] = [f'{op}{v}' for op, v in mount_values[name]]

    return {
        'compatible': len(conflicts) == 0,
        'mutual': {'flags': mutual_flags, 'values': mutual_values},
        'mkfs_only': mkfs_only,
        'mount_only': mount_only,
        'conflicts': conflicts
    }


# ---------------------------------------------------------------------------
# File processor
# ---------------------------------------------------------------------------

def process_pair(mount_path, mkfs_path):
    """Process one matched pair of opts files."""
    mnt_fs, mnt_groups = parse_opts_file(mount_path)
    mkfs_fs, mkfs_groups = parse_opts_file(mkfs_path)

    # Sanity: fs names must match
    if mnt_fs != mkfs_fs:
        print(f'  [warn] fs mismatch: "{mnt_fs}" vs "{mkfs_fs}"')
        return None

    n = min(len(mnt_groups), len(mkfs_groups))
    if len(mnt_groups) != len(mkfs_groups):
        print(f'  [warn] group count mismatch: mount={len(mnt_groups)} '
              f'mkfs={len(mkfs_groups)}, using first {n}')

    groups_out = []
    for gi in range(n):
        mnt_flags, mnt_vals = build_group_dict(mnt_groups[gi])
        mkfs_flags, mkfs_vals = build_group_dict(mkfs_groups[gi])
        grp = analyze_group(mkfs_flags, mkfs_vals, mnt_flags, mnt_vals)
        grp['group_idx'] = gi
        groups_out.append(grp)

    # Extract case index from filename
    base = os.path.basename(mkfs_path)
    m = re.search(r'mkfs_opts_(\d+)\.txt$', base)
    case_idx = m.group(1) if m else 'unknown'

    return {
        'file': os.path.basename(mount_path),
        'case_idx': case_idx,
        'filesystem': mnt_fs,
        'groups': groups_out
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    target_dir = sys.argv[1] if len(sys.argv) > 1 else os.getcwd()
    if not os.path.isdir(target_dir):
        print(f'Error: not a directory — {target_dir}')
        sys.exit(1)

    # Collect mount_opts_*.txt files (skip transformed)
    mount_files = {}
    for p in sorted(glob.glob(os.path.join(target_dir, 'mount_opts_*.txt'))):
        if '_transformed' in os.path.basename(p):
            continue
        m = re.search(r'mount_opts_(\d+)\.txt$', os.path.basename(p))
        if m:
            mount_files[m.group(1)] = p

    # Collect mkfs_opts_*.txt files (skip transformed)
    mkfs_files = {}
    for p in sorted(glob.glob(os.path.join(target_dir, 'mkfs_opts_*.txt'))):
        if '_transformed' in os.path.basename(p):
            continue
        m = re.search(r'mkfs_opts_(\d+)\.txt$', os.path.basename(p))
        if m:
            mkfs_files[m.group(1)] = p

    if not mount_files:
        print('No mount_opts_*.txt files found')
        return
    if not mkfs_files:
        print('No mkfs_opts_*.txt files found')
        return

    # Pair by caseIdx
    common = sorted(set(mount_files.keys()) & set(mkfs_files.keys()),
                    key=lambda x: int(x) if x.isdigit() else x)

    if not common:
        print('No matching caseIdx pairs found between mount_opts and mkfs_opts')
        return

    print(f'Processing {len(common)} pair(s) …')
    for ci in common:
        result = process_pair(mount_files[ci], mkfs_files[ci])
        if result is None:
            continue
        out_path = os.path.join(target_dir,
                                f'cross_dependency_{result["case_idx"]}.json')
        with open(out_path, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)
        print(f'[done]  {os.path.basename(out_path)}')


if __name__ == '__main__':
    main()
