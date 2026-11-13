"""Run in the fresh candidate checkout. Requires both review pins in Git."""
from pathlib import Path
import subprocess, json, hashlib, collections, re
a='3788009de306d80e002976e66ba2b1103e2dbd83'
b='c92c0f66360f85c0a3339ab9b30fc00c39ee5f93'
c='6f5b86c09abfcb7f9526a9d1f585c6501c023b4a'
def git(*args):return subprocess.check_output(['git',*args])
def at(h,path):return git('show',h+':'+path)
def digest(data):return hashlib.sha256(data).hexdigest()
for path in ['CFDLean/Core/Coordinates.lean','CFDLean/Core/PhysicalJacobian.lean','CFDLean/Core/PhysicalFlux.lean','CFDLean/Core/State.lean','Integrity.lean','KernelAudit.lean','lean-toolchain','lake-manifest.json','lakefile.toml','specifications/M1.md','specifications/M2.md']:
 assert at(a,path)==at(b,path);print('Preserved',path)
patch=git('diff','--full-index',a,b,'--','specifications/M2-results.json','evidence/verification.json')
assert patch==at(c,'reviews/M2b/bindings-and-types.patch')
print('Independent literal diff same as submitted:',len(patch),'bytes')
for folder in ['reviews/M2b','evidence/M2b-source-replay']:
 sums=at(c,folder+'/SHA256SUMS').decode().splitlines()
 for line in sums:
  h,f=line.split(None,1);assert digest(at(c,folder+'/'+f.strip()))==h
 print('Checkpoint manifest',folder,len(sums),'matches')
for f in ['verification.json','kernel-inventory.log','bindings-diff.patch','binding-type-diff.json','inherited-types.json']:
 p='evidence/'+f;data=Path(p).read_bytes()
 assert data==at(b,p)==at(c,'evidence/M2b-source-replay/'+f)
 print('Three-way byte match',f,digest(data))
V=json.loads(Path('evidence/verification.json').read_bytes());old=json.loads(at(a,'evidence/verification.json'))
B=json.loads(Path('specifications/M2-results.json').read_bytes());oldB=json.loads(at(a,'specifications/M2-results.json'))
J=B['results'][0];assert J==oldB['results'][0];diff=json.loads(Path('evidence/binding-type-diff.json').read_bytes())
for group in B['results']:
 for n in group['declarations']:
  row=V['declarations'][n];assert row['root'] and row['kind']=='theorem';assert row['type']==diff[n]['current_type']
  if group==J:assert old['declarations'][n]['type']==row['type']==diff[n]['accepted_type']
  else:assert diff[n]['accepted_type'] is None
  print(group['id'],n,row['type'])
assert len(diff)==len(V['promised_theorems'])==37
print('Kinds',collections.Counter((v['kind'],v['root']) for v in V['declarations'].values()))
print('Closure',V['closure'])
assert git('diff','--name-only','HEAD').decode().splitlines()==['evidence/build.log']
