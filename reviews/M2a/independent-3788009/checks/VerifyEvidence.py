"""Run with the candidate checkout as the working directory."""
import hashlib, json, pathlib, subprocess, sys
from collections import Counter
sys.path.insert(0,str(pathlib.Path('scripts').resolve()))
import verify
p=pathlib.Path
records=json.loads(p('evidence/verification.json').read_text())
submitted=p('../submitted/verification.json')
def git(*args):return subprocess.check_output(['git',*args])
for f in ['kernel-inventory.log','verification.json','SHA256SUMS']:
    data=p('evidence',f).read_bytes();assert data==git('show','HEAD:evidence/'+f)
    if f != 'SHA256SUMS':assert data==p('../submitted',f).read_bytes()
    print('Matched original candidate'+(' and checkpoint' if f!='SHA256SUMS' else ''),f,hashlib.sha256(data).hexdigest())
assert git('diff','--name-only','HEAD').decode().splitlines()==['evidence/build.log']
d=records['declarations']
print('Root classes',Counter((r['kind'],r['unsafe']) for r in d.values() if r['root']))
print('Non-root classes',Counter((r['kind'],r['unsafe']) for r in d.values() if not r['root']))
print('Closure',records['closure'])
for n in records['promised_theorems']:print(n, d[n]['type'])
contract=json.loads(p('specifications/M2-results.json').read_text())
# An in-memory coverage regression test, without modifying the candidate.
next(x for x in contract['results'] if x['id']=='M2-J')['declarations']=['CFDLean.Coordinates.area_zero']
verify.check_result_ids(contract,p('specifications/M2.md').read_text())
print('Alternative M2-J binding accepted by name-only checker:',verify.check_promises(d,contract,'M2a'))
