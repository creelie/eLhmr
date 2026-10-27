"""Compile the three current documents without generating pre-DOI ZIPs."""
from pathlib import Path
import re
import shutil
import subprocess

root = Path(__file__).resolve().parent.parent
packet = root / 'Paper_5 package'
output = root / 'build/current-submission'
tex = shutil.which('pdflatex')
assert tex, 'pdfLaTeX is required'
for component in ['manuscript-source', 'coverletter-source', 'ai-declaration-source']:
    target = output / component
    target.mkdir(parents=True, exist_ok=True)
    for _ in range(3):
        result = subprocess.run([tex, '-interaction=nonstopmode', '-halt-on-error',
                                 '-output-directory=' + str(target), 'main.tex'],
                                cwd=packet / component, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout.decode(errors='replace')[-4000:])
    log = (target / 'main.log').read_text(errors='replace')
    assert 'Overfull' not in log, component
    assert not re.search(r'There were undefined references|Citation .* undefined|Reference .* undefined', log)
    assert (target / 'main.pdf').stat().st_size > 10000
    print('COMPILED', component)
print('No source ZIPs are created by this build check.')
