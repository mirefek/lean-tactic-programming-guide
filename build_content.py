#!/usr/bin/python

"""A script to build the content for README. This script does not edit README
but it outputs the content to be copied after a Lean file was updated.
"""

files = {
    "TacticProgrammingGuide" : ("Introduction", "the basic introduction mentioned above"),
    "CustomRw" : ("Implementing `rw` from scratch", "a tactic that does a single rewrite"),
    "CustomSimp" : ("Implementing `simp` from scratch", "more advanced expression manipulation"),
}

for (fname, (label1, label2)) in files.items():
    print(f'* [{label1}]({fname}.lean): {label2}.')
    last_sec_num = 0
    with open(fname+".lean") as f:
        for i, line in enumerate(f):
            try:
                if line.startswith('## ('):
                    sec_num, title = line[4:].split(')')
                    title = title.strip()
                    sec_num = int(sec_num)
                    if sec_num != last_sec_num+1:
                        raise Exception(f"Unexpected section {sec_num}, expected {last_sec_num+1}")
                    last_sec_num = sec_num
                    print(f'  * [{title}]({fname}.lean#L{i+1})')
            except Exception as e:
                e.add_note(f"File: {fname}, Line {i+1}: {line.strip()}")
                raise
