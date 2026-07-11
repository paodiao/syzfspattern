#!/usr/bin/python3
"""
L4: mount_state_builder.py
Generates valid mount option configurations from mount_constraints_{fs}.json.
Supports --require path constraints from Analyzer.cc with comparison operators
(>=, <=, !=, >, <, =) for int and enum options.
Outputs in mount/fstab command format.
"""

import json
import re
import sys
import os

depth = 0
states_made = 0

max_depth = 0
fsname = ""
output_fmt = "mount"
require_constraints = None  # list of constraint strings from --require


# ── Constraint parsing ──

_CONSTRAINT_RE = re.compile(r'^(>=|<=|!=|>|<|=)(\S+)$')


def parse_constraint(val_str):
    """
    Return (op, value) from a constraint string like '>=5' or '!=ordered'.
    Return (None, val_str) for plain values like '5' or 'ordered' or 'enable'.
    """
    m = _CONSTRAINT_RE.match(val_str)
    if m:
        return m.group(1), m.group(2)
    return None, val_str


def enum_constrained_values(entry, op, target_name):
    """
    Return list of enum VALUE names that satisfy the comparison (op, target_name).
    Uses enum subval (numeric key) for comparison, returns enum value strings.
    """
    ev = entry.get("enum_values", {})
    if not ev:
        return []
    # Reverse map: name → int(subval)
    name_to_subval = {name: int(sv) for sv, name in ev.items()}
    if target_name not in name_to_subval:
        return list(ev.values())  # unknown target — fallback to all

    target = name_to_subval[target_name]
    result = []
    for sv, name in ev.items():
        sub = int(sv)
        ok = True
        if op == '=':
            ok = (sub == target)
        elif op == '!=':
            ok = (sub != target)
        elif op == '>':
            ok = (sub > target)
        elif op == '>=':
            ok = (sub >= target)
        elif op == '<':
            ok = (sub < target)
        elif op == '<=':
            ok = (sub <= target)
        if ok:
            result.append(name)
    return result


def int_constrained_values(entry, op, target_val):
    """
    Return list of int candidate strings that satisfy (op, target_val).
    Also respects value_range_min/max from the constraint JSON.
    """
    vmin = entry.get("value_range_min")
    vmax = entry.get("value_range_max")

    target = int(target_val)
    # Collect base candidates
    cands = set()
    if vmin is not None:
        cands.add(int(vmin))
    if vmax is not None:
        cands.add(int(vmax))
    if vmin is not None and vmax is not None:
        mid = (int(vmin) + int(vmax)) // 2
        cands.add(mid)
    if not cands:
        cands.add(1)
    # Also add target ± 1 for range coverage
    cands.add(target)
    cands.add(target + 1)
    cands.add(max(0, target - 1))

    # Filter by operation
    result = []
    for c in sorted(cands):
        ok = True
        if op == '=':
            ok = (c == target)
        elif op == '!=':
            ok = (c != target)
        elif op == '>':
            ok = (c > target)
        elif op == '>=':
            ok = (c >= target)
        elif op == '<':
            ok = (c < target)
        elif op == '<=':
            ok = (c <= target)
        # Also check value_range
        if ok and vmin is not None and c < int(vmin):
            ok = False
        if ok and vmax is not None and c > int(vmax):
            ok = False
        if ok:
            result.append(str(c))
    return result


# ── Helpers ──

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


# ── Verifier ──

def mount_verify_config(config, constraint_data):
    for name, val in config.items():
        entry = constraint_data.get(name, {})
        tv = entry.get("takes_value", "no")

        op, plain_val = parse_constraint(val)

        # 1) int value checks
        if tv == "yes":
            if op is None:
                # plain integer value
                try:
                    ival = int(plain_val)
                except (ValueError, TypeError):
                    return False
                vmin = entry.get("value_range_min")
                vmax = entry.get("value_range_max")
                if vmax is not None and ival > int(vmax):
                    return False
                if vmin is not None and ival < int(vmin):
                    return False
            else:
                # constrained int: verify the constraint is satisfiable
                vmin = entry.get("value_range_min")
                vmax = entry.get("value_range_max")
                target = int(plain_val)
                if op == '=':
                    if vmin is not None and target < int(vmin):
                        return False
                    if vmax is not None and target > int(vmax):
                        return False
                elif op == '!=':
                    pass  # always satisfiable unless single-value range
                    if vmin is not None and vmax is not None and int(vmin) == int(vmax):
                        if target == int(vmin):
                            return False
                elif op == '>' or op == '>=':
                    if vmax is not None:
                        limit = target if op == '>' else target - 1
                        if int(vmax) <= limit:
                            return False
                elif op == '<' or op == '<=':
                    if vmin is not None:
                        limit = target if op == '<' else target + 1
                        if int(vmin) >= limit:
                            return False

        # 2) enum value checks
        if tv == "enum":
            ev = entry.get("enum_values", {})
            if not ev:
                continue
            if op is None:
                # plain enum value
                if plain_val not in ev.values():
                    return False
            else:
                # constrained enum: verify the target is in the enum set
                if plain_val not in ev.values():
                    return False
                # Check that at least one enum value satisfies the constraint
                if not enum_constrained_values(entry, op, plain_val):
                    return False

        # 3) critical constraints (unchanged)
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
                    _, a = parse_constraint(val)
                    _, b = parse_constraint(ov)
                    if int(a) < int(b):
                        return False
                except (ValueError, TypeError):
                    pass
            if rel == "greater" and ov is not None:
                try:
                    _, a = parse_constraint(val)
                    _, b = parse_constraint(ov)
                    if int(a) > int(b):
                        return False
                except (ValueError, TypeError):
                    pass

    return True


# ── DFS Generator ──

def mount_generate(config, constraint_data, target_num, final_states,
                   try_ids, id_to_name, locked_set=None):
    global states_made, depth
    if locked_set is None:
        locked_set = set()

    depth += 1
    for id_val in try_ids:
        name = id_to_name.get(id_val)
        if name is None:
            continue
        if states_made >= target_num or depth > max_depth:
            depth -= 1
            return

        entry = constraint_data[name]
        locked = name in locked_set
        existing = config.get(name)
        new_cfgs = []

        if locked and existing is not None:
            # Propagate deps but don't generate new values
            next_ids = build_next_list(entry, constraint_data)
            if next_ids:
                mount_generate(config, constraint_data, target_num, final_states,
                               next_ids, id_to_name, locked_set)
            continue

        if locked:
            continue

        if existing is not None:
            tv = entry.get("takes_value", "no")
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
            tv = entry.get("takes_value", "no")
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
            if depth > 0 and mount_verify_config(cfg, constraint_data):
                states_made += 1
                print("depth: " + str(depth) + "; states made: " + str(states_made))
                print(cfg)
                print(name)
                print("")
                final_states.append(cfg)

                next_ids = build_next_list(entry, constraint_data)
                mount_generate(cfg, constraint_data, target_num, final_states,
                               next_ids, id_to_name, locked_set)

    depth -= 1


# ── Output formatters ──

def ConfigToMountCMD(config, constraint_data, fsname="ext4",
                     device="/dev/sda1", target="/mnt"):
    opts = []
    for name, val in config.items():
        entry = constraint_data.get(name, {})
        tv = entry.get("takes_value", "no")
        op, pv = parse_constraint(val)
        if tv == "no":
            opts.append(name if val == "enable" else "no" + name)
        elif tv == "yes":
            if op is None:
                opts.append(name + "=" + str(pv))
            else:
                valid = int_constrained_values(entry, op, pv)
                v = valid[0] if valid else pv
                opts.append(name + "=" + str(v))
        elif tv == "enum":
            if op is None:
                opts.append(name + "=" + str(pv))
            else:
                valid = enum_constrained_values(entry, op, pv)
                v = valid[0] if valid else pv
                opts.append(name + "=" + str(v))

    opt_str = ",".join(opts) if opts else "defaults"
    return "(mount) -t " + fsname + " -o " + opt_str + " " + device + " " + target


def ConfigToFstab(config, constraint_data, fsname="ext4",
                  device="/dev/sda1", target="/mnt"):
    opts = []
    for name, val in config.items():
        entry = constraint_data.get(name, {})
        tv = entry.get("takes_value", "no")
        op, pv = parse_constraint(val)
        if tv == "no":
            opts.append(name if val == "enable" else "no" + name)
        elif tv == "yes":
            if op is None:
                opts.append(name + "=" + str(pv))
            else:
                valid = int_constrained_values(entry, op, pv)
                v = valid[0] if valid else pv
                opts.append(name + "=" + str(v))
        elif tv == "enum":
            if op is None:
                opts.append(name + "=" + str(pv))
            else:
                valid = enum_constrained_values(entry, op, pv)
                v = valid[0] if valid else pv
                opts.append(name + "=" + str(v))

    opt_str = ",".join(opts) if opts else "defaults"
    return device + " " + target + " " + fsname + " " + opt_str + " 0 1"


# ── Main ──

def parse_require_arg(arg_str, constraint_data):
    """
    Parse --require 'commit>=5,data!=ordered' into a dict of {name: constraint_str}.
    """
    result = {}
    if not arg_str:
        return result
    for item in arg_str.split(","):
        item = item.strip()
        if not item:
            continue
        # Try to match name+op+val vs bare flag
        m = re.match(r'^([a-zA-Z_]\w*)(>=|<=|!=|>|<|=)(.*)$', item)
        if m:
            name = m.group(1)
            op = m.group(2)
            value = m.group(3)
            if name in constraint_data:
                result[name] = op + value
        else:
            # Bare flag
            if item.startswith("no"):
                name = item[2:]
                if name in constraint_data:
                    result[name] = "disable"
            else:
                if item in constraint_data:
                    result[item] = "enable"
    return result


def main(argv):
    global max_depth, fsname, output_fmt, require_constraints

    if len(sys.argv) < 4:
        print("Usage: python3 mount_state_builder.py <fsname> <max_depth> <max_states> "
              "[mount|fstab] [--require constraint_string]")
        print("  constraint_string e.g. 'commit>=5,data!=ordered,barrier'")
        return -1

    fsname = sys.argv[1]
    max_depth = int(sys.argv[2])
    max_states = int(sys.argv[3])

    # Parse optional positional arg + --require
    args = sys.argv[4:]
    i = 0
    while i < len(args):
        if args[i] == "--require":
            i += 1
            if i < len(args):
                require_constraints = args[i]
            i += 1
        elif args[i] in ("mount", "fstab"):
            output_fmt = args[i]
            i += 1
        else:
            i += 1

    constraint_file = "mount_constraints_" + fsname + ".json"
    if not os.path.exists(constraint_file):
        print("Missing " + constraint_file + " file")
        return -1

    with open(constraint_file, encoding="utf-8") as f:
        constraint_data = json.load(f)

    # Pre-populate config from --require constraints
    start_config = {}
    locked_set = set()
    if require_constraints:
        start_config = parse_require_arg(require_constraints, constraint_data)
        locked_set = set(start_config.keys())
        print("Require constraints: " + str(start_config))

    # Start with empty config — kernel has its own compile-time defaults
    final_states = []

    all_ids = sorted(entry["id"] for entry in constraint_data.values())
    id_to_name = {entry["id"]: name for name, entry in constraint_data.items()}

    mount_generate(start_config, constraint_data, max_states, final_states,
                   all_ids, id_to_name, locked_set)

    out_name = "mount_states_" + fsname + ".txt"
    with open(out_name, "w", encoding="utf-8") as output_file:
        for state in final_states:
            if output_fmt == "fstab":
                line = ConfigToFstab(state, constraint_data, fsname)
            else:
                line = ConfigToMountCMD(state, constraint_data, fsname)
            print(line)
            output_file.write(line + "\n")

    print("Generated " + str(len(final_states)) + " states -> " + out_name)


if __name__ == "__main__":
    main(sys.argv[1:])
