from pathlib import Path
import subprocess,json,hashlib,zipfile
repo=Path(__file__).resolve().parents[1]/'candidate'
base='3a586a42546cba1784cc79269e3f9d1c5d843f0c'; cand='3dcb73dce26149673f6669725fc3b371bd95defd'; checkpoint='704ddbf217571c66ea60ca05292b70071bd3183a'
def git(*a):return subprocess.check_output(['git','-C',str(repo),*a])
def blob(rev,p):return git('show',f'{rev}:{p}')
assert git('rev-parse','HEAD').decode().strip()==cand
assert git('rev-parse','HEAD^{tree}').decode().strip()=='a8e2948c2d5aa1b7478227d17a0e0ed20b87e28f'
paths=git('ls-tree','-r','--name-only',base).decode().splitlines()
protected=[p for p in paths if p.startswith('CFDLean/') or p.startswith('specifications/') or p in ['CFDLean.lean','Integrity.lean','KernelAudit.lean','StatementChecks.lean','lean-toolchain','lakefile.toml','lake-manifest.json']]
for p in protected:assert blob(base,p)==blob(cand,p),p
archives=[p for p in paths if p.startswith(('reviews/','evidence/')) and any(s in p for s in ['/independent-','/proposal-','-source-replay/'])]
for p in archives:assert blob(base,p)==blob(cand,p),p
assert (repo/'specifications/M5-proposal.md').read_bytes()==(repo.parent/'handoff/CFD_Lean_M5_Proposal.md').read_bytes()
assert not (repo/'specifications/M5.md').exists()
assert not (repo/'specifications/M5-results.json').exists()
assert not list((repo/'CFDLean').glob('Time/*'))
patch=git('diff','--full-index',base,cand)
assert patch==blob(checkpoint,'reviews/M5/Changes_from_Accepted_M4.patch')
print('Full-index patch exact match',hashlib.sha256(patch).hexdigest())
old=json.loads(blob(base,'evidence/verification.json'));new=json.loads(blob(cand,'evidence/verification.json'))
assert old['promised_theorems']==new['promised_theorems'];assert len(new['promised_theorems'])==156
for name in old['promised_theorems']:assert old['declarations'][name]['type']==new['declarations'][name]['type'],name
comparison=json.loads(blob(cand,'evidence/binding-type-diff.json'));assert len(comparison)==156
for name,row in comparison.items():assert row['accepted_type'] is not None and row['accepted_type']==row['current_type'],name
assert blob(cand,'evidence/bindings-diff.patch')==b''
assert blob(cand,'evidence/kernel-inventory.log')==blob(base,'evidence/kernel-inventory.log')
archive=repo/'reviews/M4b/independent-3a586a4';count=0
for line in (archive/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split('  ',1);assert hashlib.sha256((archive/name).read_bytes()).hexdigest()==digest;count+=1
assert count==28
original=repo.parent.parent/'deliverables/CFD_Lean_M4b_and_Full_M4_Independent_Review.zip'
with zipfile.ZipFile(original) as z:
 for p in archive.rglob('*'):
  if p.is_file():assert p.read_bytes()==z.read(p.relative_to(archive).as_posix()),p
for name in ['verification.json','kernel-inventory.log','inherited-types.json','bindings-diff.patch','binding-type-diff.json']:
 accepted=blob(base,'evidence/'+name)
 assert (archive/'replay'/name).read_bytes()==accepted
 assert (repo/'evidence/M4b-source-replay'/name).read_bytes()==accepted
print(f'{len(protected)} accepted mathematical/configuration/specification files unchanged; {len(archives)} prior archive files unchanged.')
print('All 156 ordered bindings and accepted types unchanged, zero null/changed comparisons; empty result-map diff; exact 182-example file preserved.')
print('All 28 original M4b review payload hashes and original ZIP bytes preserved. Five archived reviewer/worker outputs match accepted candidate.')
print('Standalone proposal equals pinned repository file; no M5 Lean implementation, frozen contract or active results. Separate M3 accepted pin retained.')
