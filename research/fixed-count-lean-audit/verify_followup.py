"""Check compiled evidence, semantic endpoints, and immutable source identity."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
REPO = Path(r'D:\CLAUDE PAPERS\lehmer-v2-2026-10-24\repository')
MATHLIB = Path(r'D:\CLAUDE PAPERS\research-audit-2026-10-23\polya\repository\lean\.lake\packages\mathlib')
LEAN = r'C:\Users\user\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe'
expected = ['counterexample_lt_bound', 'mem_fixedCount_iff',
            'conjecture_iff_all_fixedCount_empty', 'standard_conjecture_iff_all_fixedCount_empty',
            'first_three_counts_empty', 'last_entry_equation', 'last_entry_unique',
            'unit_deficit_forces_prefix_product', 'unit_deficit_excludes_prime_tail', 'two_entry_identity']
source = ROOT.joinpath('lean', 'UniformFinite.lean').read_text(encoding='utf-8')
log = ROOT.joinpath('logs', 'UniformFinite.log').read_text(encoding='utf-8')
run = json.loads(ROOT.joinpath('compile-results.json').read_text(encoding='utf-8'))
assert run[-1]['module'] == 'UniformFinite' and run[-1]['exit_code'] == 0
assert not re.search(r'\b(sorry|admit|axiom)\b', source)
assert 'error:' not in log and 'sorryAx' not in log and 'ofReduceBool' not in log
axioms = {}
for name in expected:
    match = re.search(r"'LehmerFollowup\." + name + r"' depends on axioms: \[([^]]*)\]", log)
    assert match, name
    used = [v.strip() for v in match.group(1).split(',') if v.strip()]
    assert set(used) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, used)
    axioms[name] = used
assert "def LehmerFollowup.Counterexample" in log and "1 < n ∧ ¬Nat.Prime n ∧ φ n ∣ n - 1" in log
assert "def LehmerFollowup.fixedCount" in log
assert '(∀ n : ℕ, 1 < n → φ n ∣ n - 1 → n.Prime) ↔ ∀ k, fixedCount k = ∅' in source

def git(*args, cwd=REPO):
    return subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True).stdout

# This immutable release/tag association was checked in the preceding
# archival audit; do not depend on a mutable local tag name.
pin = 'd1554b2f82c3893a5de17a52a8e414358a2fb04b'
assert git('rev-parse', pin + '^{commit}').decode().strip() == pin
deps = []
for name in ('Imports', 'Basic', 'Search', 'Product'):
    rel = 'lean/LehmerTotient/' + name + '.lean'
    original = git('show', pin + ':' + rel)
    local = ROOT.joinpath('lean', 'LehmerTotient', name + '.lean').read_bytes()
    assert local.replace(b'\r\n', b'\n') == original.replace(b'\r\n', b'\n')
    olean = ROOT.joinpath('lean', 'LehmerTotient', name + '.olean')
    assert olean.is_file()
    assert not ROOT.joinpath('logs', 'LehmerTotient_' + name + '.log').read_text(encoding='utf-8').strip()
    deps.append({'module': name, 'source_sha256': hashlib.sha256(local).hexdigest(),
                 'tag_git_blob': git('rev-parse', pin + ':' + rel).decode().strip(),
                 'compiled_olean_sha256': hashlib.sha256(olean.read_bytes()).hexdigest(),
                 'compiler_output_empty': True})
mathlib_pin = git('rev-parse', 'HEAD', cwd=MATHLIB).decode().strip()
assert mathlib_pin == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
version = subprocess.run([LEAN, '--version'], check=True, capture_output=True, text=True).stdout.strip()
assert '4.34.1' in version
shutil.copyfile(REPO / 'LICENSE', ROOT / 'LICENSE')
report = {'status': 'PASS: the specified partial reduction and identities',
          'full_lehmer_conjecture_proved': False, 'all_k_emptiness_proved': False,
          'python_dfs_fully_formalised': False, 'new_release_or_doi_created': False,
          'compiler': version, 'mathlib_commit': mathlib_pin,
          'source_repository': 'https://github.com/creelie/eLhmr',
          'existing_source_tag': 'v1.7.0', 'source_tag_commit': pin,
          'existing_research_doi': '10.5281/zenodo.23637442',
          'checked_theorem_count': len(expected), 'axioms': axioms,
          'prerequisites': deps, 'final_compiler_run': run[-1],
          'new_source_sha256': hashlib.sha256(ROOT.joinpath('lean', 'UniformFinite.lean').read_bytes()).hexdigest(),
          'compiler_log_sha256': hashlib.sha256(ROOT.joinpath('logs', 'UniformFinite.log').read_bytes()).hexdigest()}
ROOT.joinpath('verification-report.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
# Do not ship incidental failed-attempt or empty metadata as verification evidence.
payloads = [ROOT / 'VERIFICATION-STATUS.md', ROOT / 'LICENSE', ROOT / 'verification-report.json',
            ROOT / 'lean' / 'UniformFinite.lean', ROOT / 'logs' / 'UniformFinite.log',
            ROOT / 'prepare_lean.py', ROOT / 'compile_lean.py', ROOT / 'verify_followup.py',
            ROOT / 'compile-results.json', ROOT / 'copied-sources.json']
payloads.extend(ROOT.joinpath('lean', 'LehmerTotient', n + '.lean') for n in ('Imports', 'Basic', 'Search', 'Product'))
ROOT.joinpath('SHA256SUMS.txt').write_text(''.join(
    hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ROOT).as_posix() + '\n'
    for p in sorted(payloads)), encoding='utf-8')
print(json.dumps({k: report[k] for k in ('status', 'checked_theorem_count', 'full_lehmer_conjecture_proved',
                                      'all_k_emptiness_proved', 'source_tag_commit')}, indent=2))
