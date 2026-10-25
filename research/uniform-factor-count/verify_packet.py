"""Portable integrity gate; verifies bytes and honest status, not an open theorem."""
from pathlib import Path
import hashlib,json,sys,zipfile

n=int(sys.argv[1])
here=Path(__file__).resolve()
if here.parent.name=='research' and (here.parent.parent/'PACKAGE-MANIFEST.json').is_file():
    packet=here.parent.parent
else:
    root=next(p for p in here.parents if (p/f'Paper_{n} package').is_dir())
    packet=root/f'Paper_{n} package'
manifest=json.loads((packet/'PACKAGE-MANIFEST.json').read_text())
assert manifest['full_requested_closure_proved'] is False
for item in manifest['files']:
    p=packet/item['path']
    assert p.resolve().is_relative_to(packet.resolve())
    assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],item['path']
meta=json.loads((packet/'submission-metadata.json').read_text())
with zipfile.ZipFile(packet/meta['tex_zip']) as z:
    assert 'main.tex' in z.namelist() and not any(x.endswith('.lean') for x in z.namelist())
    if n==5:
        assert 'uniform_all_k.tex' in z.namelist() and 'anc/uniform_tree.py' in z.namelist()
print(json.dumps({'status':'PASS','paper':n,'payloads':len(manifest['files']),
                  'full_requested_closure_proved':False}))
