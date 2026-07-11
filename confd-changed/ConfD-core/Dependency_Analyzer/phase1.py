import operator as op
import sys
import json
import os
import glob
import subprocess

###################################################
fs_name = os.environ.get("CONFD_FS_NAME", "ext4")
params_file = os.path.join("..", "Taint_Analyzer", fs_name + "_constraints_parameters.json")
input_json = open(params_file, "r")
data = json.load(input_json)


####################################################
#value Type
####################################################

def value_type_identify(line):
    for line1 in line:
        if "Data type = " in line1:
            result = line1.split("Data type = ", 1)[1].strip()
            return result

def value_type_extract(files,json_dic):
    for file_name in files:
        tmp=json_dic[file_name]
        tmp["value_type"] = value_type_identify(files[file_name])
        tmp1 = data[file_name]
        tmp["flag"] = tmp1["flag"]
        tmp["takes_value"] = tmp1["takes_value"]
        tmp["variable"] = tmp1.get("variable")
    return json_dic

#######################################################
#Data Range constraint extract
#######################################################

def value_range_max_identify(line):
    for line1 in line:
        if "Max value = " in line1:
            parts = line1.split(' ')
            val = parts[4]
            # Handle " - 1" suffix from UGE/SGE/FCMP_OGT predicates
            # Output format: "Max value = i32 65535 - 1" → actual max is 65534
            if len(parts) >= 7 and parts[5] == '-' and parts[6] == '1':
                return str(int(val) - 1)
            return val

def value_range_min_identify(line):
    for line1 in line:
        if "Min value = " in line1:
            parts = line1.split(' ')
            val = parts[4]
            # Handle "+ 1" suffix from ULE/SLE/OLT predicates
            # Output format: "Min value = i32 5+ 1" → actual min is 6
            if len(parts) >= 7 and parts[5] == '+' and parts[6] == '1':
                return str(int(val.rstrip('+')) + 1)
            return val

def whole_constrint(files,json_dic):
    for file_name in files:
        tmp=json_dic[file_name]
        tmp["value_range_max"] = value_range_max_identify(files[file_name])
        tmp["value_range_min"] = value_range_min_identify(files[file_name])
    return json_dic

####################################################
#trace comparison for dependency
####################################################

def depen_error_line(file1, file2):
    """Check if two trace files share a com_err/fprintf error line.
    Used by Trace_whole_compare to flag pairs needing Phase 2 analysis."""
    error_markers = ("@com_err", "@fprintf", "@printf",
                     "@error", "@do_abort", "@do_error")
    for line1 in file1:
        for line2 in file2:
            line1_s = line1.replace(" ", "")
            line2_s = line2.replace(" ", "")
            if line1_s == line2_s:
                for marker in error_markers:
                    if marker in line1_s:
                        return True
    return False


def dic_revise(json_dic, file_name1, file_name2, has_error=False):  #update json_dic dependency
    #update trace1
    tmp_dic1=json_dic[file_name1].copy()
    tmp1_arr=tmp_dic1["dependency"].copy()
    if file_name2 not in tmp1_arr:
        tmp1_arr.append(file_name2)
    tmp_dic1["dependency"]=tmp1_arr
    if has_error:
        tmp1_crit=tmp_dic1["crit_candidate"].copy()
        if file_name2 not in tmp1_crit:
            tmp1_crit.append(file_name2)
        tmp_dic1["crit_candidate"]=tmp1_crit
    json_dic[file_name1]=tmp_dic1
    #update trace2
    tmp_dic2 = json_dic[file_name2].copy()
    tmp2_arr=tmp_dic2["dependency"].copy()
    if file_name1 not in tmp2_arr:
        tmp2_arr.append(file_name1)
    tmp_dic2["dependency"]=tmp2_arr
    if has_error:
        tmp2_crit=tmp_dic2["crit_candidate"].copy()
        if file_name1 not in tmp2_crit:
            tmp2_crit.append(file_name1)
        tmp_dic2["crit_candidate"]=tmp2_crit
    json_dic[file_name2]=tmp_dic2
    return json_dic


def Trace_compare(file1,file2, f1_name, f2_name):
    """Compare two taint traces. Returns (dependency_name_or_False, has_error_path)."""
    found_dep = False
    has_error = False
    for line1 in file1:
        for line2 in file2:
            if line1 == line2:
                print ("found common line")
                if "@com_err" in line1 or "@fprintf" in line1 or \
                   "@printf" in line1 or "@error" in line1 or \
                   "@do_abort" in line1 or "@do_error" in line1:
                    print ("found error line")
                    has_error = True
                    text_file = open(os.path.join("dependent", f1_name + f2_name), "w")
                    n = text_file.write(line1)
                    text_file.close()
                if not found_dep:
                    if "Data type =" not in line1 and "Max value =" not in line1 and "Min value =" not in line1:
                        found_dep = True
                if found_dep and has_error:
                    break
    return (f2_name if found_dep else False, has_error)


def Trace_whole_compare(files,json_dic):
    file_arr=[]
    file_name_arr=[]
    for file_name in files:
        file_arr.append(file_content_dic[file_name])
        file_name_arr.append(file_name)
    for i in range(len(file_arr)-1):
        for j in range(i+1, len(file_arr)):
            print(file_name_arr[i])
            dep_name, has_err = Trace_compare(file_arr[i], file_arr[j],
                                              file_name_arr[i], file_name_arr[j])
            if dep_name:
                json_dic=dic_revise(json_dic, file_name_arr[i], file_name_arr[j],
                                    has_error=has_err)
    return json_dic

####################################################
#silent dependency detection
####################################################

# Set/clear function name patterns for known FS tools
# Format: (set_pattern, clear_pattern)
SILENT_PATTERNS = [
    # e2fsprogs
    ("ext2fs_set_feature_", "ext2fs_clear_feature_"),
    ("ext2fs_mark_", "ext2fs_unmark_"),
    # xfsprogs (libxfs)
    ("xfs_sb_version_add", "xfs_sb_version_remove"),
    ("xfs_add_", "xfs_remove_"),
    # btrfs-progs
    ("btrfs_set_super_", "btrfs_clear_super_"),
    ("btrfs_set_feature_", "btrfs_clear_feature_"),
    # ntfsprogs (flags-based, fewer explicit set/clear functions)
    ("ntfs_volume_set_", "ntfs_volume_clear_"),
    # exfatprogs (minimal feature flags, mostly numerical constraints)
    ("exfat_set_", "exfat_clear_"),
    # f2fstools
    ("f2fs_set_feature_", "f2fs_clear_feature_"),
    ("f2fs_enable_", "f2fs_disable_"),
    # erofsutils
    ("erofs_set_", "erofs_clear_"),
    # generic fallback — lowest priority
    ("set_", "clear_"),
]

def extract_target_from_line(line, prefix):
    """Extract the target name from a 'prefix_TARGET(' pattern in a LLVM IR line."""
    idx = line.find(prefix)
    if idx < 0:
        return None
    start = idx + len(prefix)
    end = start
    while end < len(line) and (line[end].isalnum() or line[end] == '_'):
        end += 1
    return line[start:end]

def detect_silent_deps(files, json_dic):
    """Scan taint traces for silent set/clear dependency patterns.
    If param A's trace calls 'set_feature_B', record A → B (enable).
    If param A's trace calls 'clear_feature_B', record A → B (disable)."""
    for file_name, param_info in json_dic.items():
        silent_list = param_info.get("silent_dep", [])
        for line in files[file_name]:
            for set_pat, clear_pat in SILENT_PATTERNS:
                target = extract_target_from_line(line, set_pat)
                if target and target != file_name:
                    entry = target + ":enable"
                    if entry not in silent_list:
                        silent_list.append(entry)
                target = extract_target_from_line(line, clear_pat)
                if target and target != file_name:
                    entry = target + ":disable"
                    if entry not in silent_list:
                        silent_list.append(entry)
        param_info["silent_dep"] = silent_list
    return json_dic


####################################################
#main run
####################################################################

default_dic={"id": 0,
                "flag": None,
                "value_type": "unknown",
                "takes_value": None,
                "value_range_max": None,
                "value_range_min": None,
                "dependency":[],
                "silent_dep": [],
                "crit_candidate": [],
                "variable": None}

def expand_args(argv):
    out = [argv[0]]
    for arg in argv[1:]:
        if os.path.isdir(arg):
            out.extend(sorted(glob.glob(os.path.join(arg, '*.trace'))))
        else:
            out.append(arg)
    return out


def read_files(argv):#get default dic and file lines
    file={}
    json_dic = {}
    for i in range(1,len(argv)):
        arg = argv[i]
        name = os.path.splitext(os.path.basename(arg))[0]
        tmp_dic=default_dic.copy()
        tmp_dic["id"]=i
        if name in data:
            seed_entry = data[name]
            if seed_entry.get("dependency"):
                tmp_dic["dependency"] = list(seed_entry["dependency"])
            if seed_entry.get("silent_dep"):
                tmp_dic["silent_dep"] = list(seed_entry["silent_dep"])
        json_dic[name]=tmp_dic
        with open(arg, "r") as c:
            file[name] = c.read().splitlines()
    return file,json_dic

###########################################################
#main run
###########################################################

print(sys.argv)
print(len(sys.argv))

expanded = expand_args(sys.argv)
os.makedirs("dependent", exist_ok=True)
file_content_dic,json_dic=read_files(expanded) #get default dic and file lines
json_dic=value_type_extract(file_content_dic,json_dic)
json_dic=whole_constrint(file_content_dic,json_dic) #revise icmp contraint

if len(expanded) > 2:
    json_dic=Trace_whole_compare(file_content_dic,json_dic) ## extract dependency and revise dependency

json_dic=detect_silent_deps(file_content_dic,json_dic)  # detect silent set/clear dependencies

with open('result.json', 'w') as f:             #json file write
        json.dump(json_dic, f, ensure_ascii=False, indent=4)

#print(file_content_dic)
print(json_dic)
