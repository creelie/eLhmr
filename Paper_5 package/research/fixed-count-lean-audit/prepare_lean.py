"""Stage a small audit without modifying the released repository or dependencies."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parent
UPSTREAM = Path(r'D:\CLAUDE PAPERS\lehmer-v2-2026-10-24\repository\lean')
PACKAGES = Path(r'D:\CLAUDE PAPERS\research-audit-2026-10-23\polya\repository\lean\.lake\packages')
ROOT.joinpath('lean', 'LehmerTotient').mkdir(parents=True, exist_ok=True)
sources = []
for name in ('Imports', 'Basic', 'Search', 'Product'):
    rel = Path('LehmerTotient', name + '.lean')
    src, dst = UPSTREAM / rel, ROOT / 'lean' / rel
    shutil.copyfile(src, dst)
    sources.append({'file': rel.as_posix(), 'sha256': hashlib.sha256(src.read_bytes()).hexdigest()})
paths = [str(ROOT / 'lean')]
for directory in sorted(PACKAGES.iterdir()):
    lib = directory / '.lake' / 'build' / 'lib' / 'lean'
    if lib.is_dir():
        paths.append(str(lib))
ROOT.joinpath('lean-path.txt').write_text(';'.join(paths), encoding='utf-8')
ROOT.joinpath('copied-sources.json').write_text(json.dumps(sources, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'copied_modules': len(sources), 'cached_library_paths': len(paths) - 1}))
