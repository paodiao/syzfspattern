#!/usr/bin/python3

import json
import copy
import sys
import random
import os

depth = 0
states_made = 0

max_depth = 0
misspell = False

class Configuration:
    arg = None
    
    def __init__(self, defaults=None):
        self.arg = dict()
        if defaults:
            for a in defaults:
                self.arg[a] = defaults[a]

#finds next largest number power of 2
def nextPow2(n):
    n = n - 1
    while n & n - 1:
        n = n & n - 1
    return n << 1

#looks up by id for constraint_data
def id_lookup(constraint_data, id):
    for i in constraint_data:
        if constraint_data[i]['id'] == id:
            return i

#Takes command line style config, adds params to existing Configuration
def read_config(line, my_config):
    params = line.split(' -')
    for param in params:
        if param != "(mke2fs)" and param != "\n" and param[0] != 'O':
            key = param.strip().split(' ')[0]
            val = param.strip().split(' ')[1]
            my_config.arg[reverse_argument_key["-" + key]] = val
        elif param[0] == 'O':
            clean = param.strip().split(' ')[1].split(',')
            for c in clean:
                my_config.arg[c] = ""

#Determines if a given Configuration is valid within given constraints
def verify_config(my_config, constraint_data):
    for a in my_config.arg:
        entry = constraint_data.get(a, {})
        if entry.get("takes_value") == "yes":
            vmin = entry.get("value_range_min")
            vmax = entry.get("value_range_max")
            if vmax is not None and int(vmax) < int(my_config.arg[a]):
                return False
            if vmin is not None and int(vmin) > int(my_config.arg[a]):
                return False
    
    for a in my_config.arg:
        entry = constraint_data.get(a, {})
        crit = entry.get("critical", None)
        if crit is not None:
            for other, rel in crit.items():
                ov = my_config.arg.get(other)
                if rel == "enable" and (ov is None or ov == "disable"):
                    return False
                if rel == "disable" and ov == "enable":
                    return False
                if rel == "smaller" and ov is not None:
                    if int(my_config.arg[a]) < int(ov):
                        return False
                if rel == "greater" and ov is not None:
                    if int(my_config.arg[a]) > int(ov):
                        return False
                if rel == "mutual_exclusion" and ov == "enable" and my_config.arg[a] == "enable":
                    return False
    return True
    
#Generates states up to target number 
def generate(my_config, constraint_data, target_num, final_states, invalid_states, try_list, defaults):
    global states_made
    global depth
    global misspell
    depth += 1
    for id in try_list:
        name = id_lookup(constraint_data, id)
        if name is None:
            continue
        if states_made >= target_num:
            depth -= 1
            return
        if depth > max_depth:
            depth -= 1
            return
        
        entry = constraint_data[name]
        new_configs = []
        temp = copy.deepcopy(my_config)
        new_configs.append(temp)
        
        existing = my_config.arg.get(name)
        if existing is not None:
            if defaults is not None and defaults.get(name) is not None:
                tv = entry.get("takes_value", "no")
                if tv == "no" or tv == "flag_only":
                    if existing == "enable":
                        temp.arg[name] = "disable"
                    else:
                        temp.arg[name] = "enable"
                elif tv == "enum":
                    ev = entry.get("enum_values", {})
                    vals = [v for v in ev.values() if v != existing]
                    new_configs = [new_configs[0]]
                    for v in vals:
                        cfg = copy.deepcopy(my_config)
                        cfg.arg[name] = v
                        new_configs.append(cfg)
                    new_configs.pop(0)
                elif entry.get("value_range_min") is not None:
                    vmin = entry["value_range_min"]
                    vmax = entry.get("value_range_max")
                    if vmax is not None:
                        temp2 = copy.deepcopy(my_config)
                        new_configs.append(temp2)
                        temp3 = copy.deepcopy(my_config)
                        new_configs.append(temp3)
                        temp.arg[name] = vmin
                        temp2.arg[name] = vmax
                        temp3.arg[name] = nextPow2(int(vmin) + 1)
                    else:
                        temp.arg[name] = vmin
                else:
                    if entry.get("value_range_max") is not None:
                        temp.arg[name] = entry["value_range_max"]
                    else:
                        temp.arg[name] = 1
            else:
                continue
        else:
            tv = entry.get("takes_value", "no")
            if tv == "no" or tv == "flag_only":
                temp.arg[name] = "enable"
            elif tv == "enum":
                ev = entry.get("enum_values", {})
                vals = list(ev.values())
                new_configs = [new_configs[0]]
                for v in vals:
                    cfg = copy.deepcopy(my_config)
                    cfg.arg[name] = v
                    new_configs.append(cfg)
                new_configs.pop(0)
            elif entry.get("value_range_min") is not None:
                vmin = entry["value_range_min"]
                vmax = entry.get("value_range_max")
                if vmax is not None:
                    temp2 = copy.deepcopy(my_config)
                    new_configs.append(temp2)
                    temp3 = copy.deepcopy(my_config)
                    new_configs.append(temp3)
                    temp.arg[name] = vmin
                    temp2.arg[name] = vmax
                    temp3.arg[name] = nextPow2(int(vmin) + 1)
                else:
                    temp.arg[name] = vmin
            else:
                if entry.get("value_range_max") is not None:
                    temp2 = copy.deepcopy(my_config)
                    new_configs.append(temp2)
                    temp.arg[name] = entry["value_range_max"]
                    temp2.arg[name] = 1
                else:
                    temp.arg[name] = 1
        
        for temp_config in new_configs:
            seen = False
            for past in final_states:
                if past.arg == temp_config.arg:
                    seen = True
            if not seen:
                if depth > 0 and verify_config(temp_config, constraint_data):
                    states_made += 1
                    print("depth: " + str(depth) + "; states made: " + str(states_made))
                    print(temp_config.arg)
                    print(name)
                    print("")
                    final_states.append(temp_config)
                    
                    if misspell:
                        word = random.choice(list(temp_config.arg))
                        entry_w = constraint_data.get(word, {})
                        if entry_w.get("flag") == "-O":
                            mis_copy = copy.deepcopy(temp_config)
                            mis_copy.arg.pop(word, None)
                            replace_num = random.randint(0, len(word) - 1)
                            word = word[:replace_num] + chr(ord(word[replace_num]) + 1) + word[replace_num + 1:]
                            mis_copy.arg[word] = "enable"
                            invalid_states.append(mis_copy)
                else:
                    seen2 = False
                    for past in invalid_states:
                        if past.arg == temp_config.arg:
                            seen2 = True
                    if not seen2:
                        invalid_states.append(temp_config)
                
                next_list = []
                for dep in entry.get("dependency", []):
                    if dep in constraint_data:
                        next_list.append(constraint_data[dep]["id"])
                crit = entry.get("critical", {})
                if crit:
                    for cname in crit.keys():
                        if cname in constraint_data:
                            next_list.append(constraint_data[cname]["id"])
                for sentry in entry.get("silent_dep", []):
                    target = sentry.split(":")[0] if ":" in sentry else sentry
                    if target in constraint_data:
                        next_list.append(constraint_data[target]["id"])
                
                generate(temp_config, constraint_data, target_num, final_states, invalid_states, next_list, defaults)
    
    depth -= 1


# Converts from Configuration to command line style (cross-filesystem)
def ConfigToCMD(config, constraint_data, tool_name="mke2fs"):
    output = "(" + tool_name + ")"
    groups = {}
    
    for arg, val in config.arg.items():
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
            if val == "enable":
                groups[base].append(arg)
            else:
                groups[base].append("^" + arg)
        elif tv == "flag_only":
            output += " " + base
            continue
        else:
            frag = key + "=" + str(val) if key else str(val)
            groups[base].append(frag)
    
    for base, items in groups.items():
        output += " " + base + " " + ",".join(items)
    
    return output


def main(argv):
    global max_depth
    global misspell
    
    constraints_file = os.environ.get("CONFD_CONSTRAINTS_JSON", "mke2fs_constraints.json")
    defaults_file = os.environ.get("CONFD_DEFAULT_CONFIG", "default_config.json")
    tool_name = os.environ.get("CONFD_TOOL_NAME", "mke2fs")
    
    if not os.path.exists(constraints_file):
        print("Missing " + constraints_file + " file")
        return -1
    
    if not os.path.exists(defaults_file):
        print("Missing " + defaults_file + " file")
        return -1
        
    if len(sys.argv) != 4:
        print("Usage: python3 violate_config_state_builder.py <max_depth> <max_states> <misspell>")
        print("Environment variables:")
        print("  CONFD_CONSTRAINTS_JSON  — constraints JSON file")
        print("  CONFD_DEFAULT_CONFIG    — default config JSON file")
        print("  CONFD_TOOL_NAME         — tool name for command prefix")
        return -1
        
    max_depth = int(sys.argv[1])
    max_final_states = int(sys.argv[2])
    
    if sys.argv[3] == "True" or sys.argv[3] == "true":
        misspell = True
    
    with open(constraints_file, encoding="utf-8") as f:
        constraint_data = json.load(f)
    
    with open(defaults_file, encoding="utf-8") as f:
        defaults = json.load(f)
    
    my_config = Configuration(defaults)
    final_states = []
    invalid_states = []
    
    all_ids = sorted(entry["id"] for entry in constraint_data.values())
    
    generate(copy.deepcopy(my_config), constraint_data, max_final_states, final_states, invalid_states, all_ids, defaults)
    
    print("Final (Invalid) States")
    with open("output_bad.txt", "w", encoding="utf-8") as output_file:
        for state in invalid_states:
            line = ConfigToCMD(state, constraint_data, tool_name)
            print(line)
            output_file.write(line + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])
