"""Verify current package integrity and its accurately limited proof scope."""
from pathlib import Path
import hashlib
import json
import re
import sys
import zipfile

n = int(sys.argv[1])
assert n == 5
root = next(p for p in Path(__file__).resolve().parents if (p / 'Paper_5 package').is_dir())
packet = root / 'Paper_5 package'
manifest = json.loads((packet / 'PACKAGE-MANIFEST.json').read_text(encoding='utf-8'))
assert manifest['full_requested_closure_proved'] is False
for item in manifest['files']:
    path = packet / item['path']
    assert path.resolve().is_relative_to(packet.resolve())
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item['sha256'], item['path']
meta = json.loads((packet / 'submission-metadata.json').read_text(encoding='utf-8'))
report = json.loads((packet / 'build-verification.json').read_text(encoding='utf-8'))
assert report['visual_review_complete'] is True
assert report['full_Lehmer_closure'] is False
source = packet / 'manuscript-source'
main = (source / 'main.tex').read_text(encoding='utf-8')
assert r'\documentclass[11pt,reqno]{amsart}' in main
assert not re.search(r'\\(?:linenumbers|runninglinenumbers|pagewiselinenumbers)\b', main)
assert (source / 'uniform_all_k.tex').is_file()
assert (source / 'final_prime_appendix.tex').is_file()
assert (source / 'anc/uniform_tree.py').is_file()
assert 'full Lehmer conjecture is not resolved' in re.sub(r'\s+', ' ', main)
if meta['new_doi'] is None:
    assert not list(packet.rglob('*.zip')), 'ZIP creation must follow the new confirmed DOI'
    archive_status = 'source prepared; DOI and ZIPs pending'
else:
    receipt = json.loads((packet / 'DOI-RECEIPT.json').read_text(encoding='utf-8'))
    assert receipt['published'] is True and receipt['doi'] == meta['new_doi']
    assert receipt['version'] == meta['version']
    with zipfile.ZipFile(packet / meta['tex_zip']) as archive:
        expected = {p.relative_to(source).as_posix(): p for p in source.rglob('*') if p.is_file()}
        assert set(archive.namelist()) == set(expected)
        assert not any(name.endswith('.lean') for name in archive.namelist())
        for name, path in expected.items():
            assert archive.read(name) == path.read_bytes(), name
    archive_status = 'published DOI and matching source ZIP'
print(json.dumps({'status': 'PASS', 'paper': n, 'payloads': len(manifest['files']),
                  'archive_status': archive_status, 'full_requested_closure_proved': False}))
