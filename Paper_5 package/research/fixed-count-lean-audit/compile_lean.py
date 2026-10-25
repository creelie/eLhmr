"""Compile in dependency order and preserve genuine compiler/axiom output."""
from pathlib import Path
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
LEAN = r'C:\Users\user\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe'
env = dict(os.environ)
env['LEAN_PATH'] = ROOT.joinpath('lean-path.txt').read_text(encoding='utf-8')
names = sys.argv[1:] or ['LehmerTotient/Imports', 'LehmerTotient/Basic',
                         'LehmerTotient/Search', 'LehmerTotient/Product', 'UniformFinite']
ROOT.joinpath('logs').mkdir(exist_ok=True)
results = []
for name in names:
    start = time.monotonic()
    print('Checking ' + name, flush=True)
    run = subprocess.run([LEAN, '-o', name + '.olean', name + '.lean'],
                         cwd=ROOT / 'lean', env=env, capture_output=True, text=True,
                         encoding='utf-8', errors='replace')
    ROOT.joinpath('logs', name.replace('/', '_') + '.log').write_text(run.stdout + run.stderr, encoding='utf-8')
    item = {'module': name, 'exit_code': run.returncode, 'seconds': round(time.monotonic() - start, 2)}
    if run.returncode == 0 and any(word in run.stdout + run.stderr for word in ('sorryAx', 'ofReduceBool')):
        item['exit_code'] = 1
        item['rejected_axiom_output'] = True
    results.append(item)
    print(json.dumps(item), flush=True)
    if item['exit_code']:
        print((run.stdout + run.stderr)[-12000:], flush=True)
        break
ROOT.joinpath('compile-results.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
sys.exit(any(r['exit_code'] != 0 for r in results))
