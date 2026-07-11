import json
import os
import subprocess
import sys

# ── Per-FS configuration ──
FS_CONFIG = {
    'ext4':  {'json': 'mke2fs_constraints.json',    'll': 'mke2fs.ll',
              'noise': ['retval','retval1','tmp','r_opt',
                        'force','quiet','verbose','direct_io','errors_behavior',
                        'creator_os','cflag','undo_file','mount_dir','fs_types',
                        'sync_kludge','noaction','proceed_delay','super_only']},
    'xfs':   {'json': 'mkfs_xfs_constraints.json',   'll': 'mkfs.xfs.ll',
              'noise': ['retval','tmp','tmp1','quiet']},
    'btrfs': {'json': 'mkfs_btrfs_constraints.json', 'll': 'mkfs.btrfs.ll',
              'noise': ['retval','opt_zero_end']},
    'ntfs3': {'json': 'mkntfs3_constraints.json',    'll': 'mkntfs.ll',
              'noise': ['retval']},
    'erofs': {'json': 'mkfs_erofs_constraints.json', 'll': 'mkfs.erofs.ll',
              'noise': ['retval','endptr','incremental_mode','valid_fixeduuid']},
}

fs_name = os.environ.get("CONFD_FS_NAME", "ext4")
if fs_name not in FS_CONFIG:
    print("Unknown FS name: " + fs_name)
    print("Available: " + ", ".join(FS_CONFIG.keys()))
    sys.exit(1)
cfg = FS_CONFIG[fs_name]

###### try to keep all the files in build dir
seed_json = os.environ.get("CONFD_SEED_JSON", cfg['json'])
with open(seed_json, encoding="utf-8") as f:
    data = json.load(f)

print (data['function_name'])
with open("function_name", "w", encoding="utf-8") as f1:
    f1.write(data['function_name'])

print (data['superblock'])
with open("superblock", "w", encoding="utf-8") as f2:
    f2.write(data['superblock'])

params_file = fs_name + "_constraints_parameters.json"
with open(params_file, "w", encoding="utf-8") as outfile:
    json.dump(data['parameters'], outfile, indent=4)

# Auto-generate exclude_vars: seed JSON variables + FS-specific noise
excludes = set()
for key in data['parameters']:
    v = data['parameters'][key].get("variable", "")
    if v:
        excludes.add(v)
for name in cfg['noise']:
    excludes.add(name)

with open("exclude_vars", "w", encoding="utf-8") as f_excl:
    for name in sorted(excludes):
        f_excl.write(name + "\n")

opt_bin = os.environ.get("CONFD_OPT_PATH", "llvm-project-llvmorg-14.0.0/build/bin/opt")
opt_lib = os.environ.get("CONFD_OPT_LIB_PATH", "llvm-project-llvmorg-14.0.0/build/lib/libinterProPass.so")
ll_file = os.environ.get("CONFD_LL_FILE", cfg['ll'])

for key in data['parameters']:
    print (key)
    with open("file_name", "w", encoding="utf-8") as f3:
        f3.write(key)
    for i in data['parameters'].get(key):
        if i == "variable":
            print (data['parameters'].get(key).get(i))
            with open("variable", "w", encoding="utf-8") as f4:
                f4.write(data['parameters'].get(key).get(i))
            print ("-----")
            # Build env with CONFD_* variables
            env = os.environ.copy()
            env["CONFD_TRACE_FILE"] = "file_name"
            env["CONFD_FUNC_NAME"] = data["function_name"]
            env["CONFD_VAR_NAME"]  = "variable"
            env["CONFD_EXCLUDE_FILE"] = "exclude_vars"
            subprocess.run([opt_bin, "-load", opt_lib, "-enable-new-pm=0",
                            "-interpro", ll_file], env=env)
            os.remove("file_name")
            os.remove("variable")
