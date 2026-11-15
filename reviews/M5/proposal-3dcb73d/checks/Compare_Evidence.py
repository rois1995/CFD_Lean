from pathlib import Path
import hashlib,json,subprocess
repo=Path(__file__).resolve().parents[1]/'candidate';check=repo.parent/'checks';lines=[]
for name in ['verification.json','kernel-inventory.log','inherited-types.json','bindings-diff.patch','binding-type-diff.json']:
 data=(repo/'evidence'/name).read_bytes();assert data==subprocess.check_output(['git','-C',str(repo),'show','HEAD:evidence/'+name]);lines.append('Exact candidate match '+name+' '+hashlib.sha256(data).hexdigest())
assert len((check/'Source-hashes.log').read_text().splitlines())==64
assert all(x.endswith(': OK') for x in (check/'Source-hashes.log').read_text().splitlines())
assert (check/'Tracked-diff.log').read_text()==''
v=json.loads((repo/'evidence/verification.json').read_text());assert len(v['promised_theorems'])==156
rows=v['declarations'];assert len(rows)==1726
assert v['closure']=={'visited':21175,'unsafe_reached':[],'roots':988,'axioms':['propext','Classical.choice','Quot.sound']}
assert sum(r['root'] for r in rows.values())==988
assert sum(bool(r['unsafe']) and not r['root'] for r in rows.values())==459
assert sum(not r['unsafe'] and not r['root'] for r in rows.values())==279
lines.append('64 source checksums pass; no tracked diff. Inventory/closure/counters unchanged.')
(check/'Candidate-comparison.log').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines))
