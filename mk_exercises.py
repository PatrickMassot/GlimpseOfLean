#!/usr/bin/env python3

import regex
from pathlib import Path

# In the source files, blocks of lines enclosed between two lines
# `-- sorry`
# will be replaced by a single sorry in the solutions
# Also, on a single line, `/- inline sorry -/Ioo (-1) 1/- inline sorry -/`
# will be replaced with `sorry`

inline_sorry_regex = regex.compile(r'/- inline sorry -/.*/- inline sorry -/')
sorry_regex = regex.compile(r'(.*)-- sorry.*')
omit_regex = regex.compile(r'(.*)-- omit.*')
root = Path(__file__).parent/'GlimpseOfLean'

if __name__ == '__main__':
    for path in (root/'Solutions').glob('**/*.lean'):
        print(path)
        out = root/'Exercises'/path.relative_to(root/'Solutions')
        out.parent.mkdir(exist_ok=True)
        with out.open('w', encoding="utf8") as outp:
            with path.open(encoding="utf8") as inp:
                state = 'normal'
                for line in inp:
                    line, _ = inline_sorry_regex.subn("sorry", line)

                    match_sorry = sorry_regex.match(line)
                    match_omit = omit_regex.match(line)
                    if state == 'normal':
                        if match_sorry or match_omit:
                            state = 'sorry'
                        else:
                            outp.write(line)
                    else:
                        if match_sorry:
                            state = 'normal'
                            outp.write(match_sorry.group(1) + 'sorry\n')
                        else:
                            if match_omit :
                                state = 'normal'
                                outp.write(match_omit.group(1) + '\n')

            outp.write('\n')
