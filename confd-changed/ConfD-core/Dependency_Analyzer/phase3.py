import sys
import json

###########################################
# load final json file
# input: final json file, critical dependency file
###########################################
def read_json(argv):
    with open(argv) as json_file:
        data = json.load(json_file)
        return data

##########################################
#   reverse-lookup param name via variable field
##########################################
def resolve_param(name, dic):
    """Resolve a trace_analyzer output name to the ConfD parameter key.
    Strips @ and % prefixes (getNameOrAsOperand may include them),
    then matches against JSON key or each entry's 'variable' field."""
    clean = name.lstrip('@%')
    if clean in dic:
        return clean
    for key, info in dic.items():
        if info.get("variable") == clean:
            return key
    return None

##########################################
#   revise final json file
##########################################
def revise_dic(dic, argv):
    with open(argv, "r") as c:
        lines = c.read().splitlines()
    for line in lines:
        print(line)
        tmp = line.split(" ")
        print(tmp[0])
        if len(tmp) != 3:
            print("The critical line format is invalid (expected 3 parts)")
            continue

        raw1, raw2, rel = tmp[0], tmp[1], tmp[2]

        # Resolve trace_analyzer names → ConfD parameter keys
        param1 = resolve_param(raw1, dic)
        param2 = resolve_param(raw2, dic)
        if param1 is None:
            print("Parameter '%s' not found in JSON (no key or variable match), skipping" % raw1)
            continue
        if param2 is None:
            print("Parameter '%s' not found in JSON (no key or variable match), skipping" % raw2)
            continue

        org = dic[param1]

        # Normalize relationship names from trace_analyzer output:
        #   "greater" = ICMP_UGT(op3,op4) → op3>op4 is error → op3<op4 required → "smaller"
        #   "lesser"  = ICMP_ULT(op3,op4) → op3<op4 is error → op3>op4 required → "greater"
        if rel == "greater":
            rel = "smaller"
        elif rel == "lesser":
            rel = "greater"

        # Add to critical field
        if "critical" not in org:
            org["critical"] = {}
        if param2 in org["critical"]:
            print("Existing in critical: %s" % param2)
            continue

        # Remove from dependency list (upgraded to critical)
        deps = org.get("dependency", [])
        if param2 in deps:
            deps.remove(param2)
        else:
            print("not in dependency: %s (newly discovered, adding)" % param2)
            deps.append(param2)

        org["critical"][param2] = rel

    return dic

##########################################
#                main
##########################################
print(sys.argv)
print(len(sys.argv))
if len(sys.argv) == 3:
    dic = read_json(sys.argv[1])
    dic = revise_dic(dic, sys.argv[2])
else:
    print("Usage: python3 phase3.py result.json critical_file")
    sys.exit(1)
with open(sys.argv[1], 'w') as f:
    json.dump(dic, f, ensure_ascii=False, indent=4)
print(dic)
