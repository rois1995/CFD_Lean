"""Exercise the frozen verifier's parser in isolation, without rerunning its build."""
import ast
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
filename = root / 'scripts/verify.py'
tree = ast.parse(filename.read_text())
# Only the compiled regex and pure parser function are needed.
keep = [n for n in tree.body if
        isinstance(n, ast.FunctionDef) and n.name == 'parse_axioms' or
        isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)
        and n.targets[0].id == 'PATTERN']
ns = {'re': re}
exec(compile(ast.Module(body=keep, type_ignores=[]), str(filename), 'exec'), ns)
parse = ns['parse_axioms']
from_log = parse((root / 'evidence/axioms.log').read_text())
vs = json.loads((root / 'evidence/verification.json').read_text())['transitive_axioms']
assert from_log == {name: set(axioms) for name, axioms in vs.items()}
assert parse("'CFDLean.sample' does not depend on any axioms") == {'sample': set()}
assert parse("'CFDLean.sample' depends on axioms: [propext,\n Quot.sound]") == {'sample': {'propext', 'Quot.sound'}}
assert parse("'CFDLean.sample' depends on axioms: [sorryAx]") == {'sample': {'sorryAx'}}
assert len(re.findall(r"'CFDLean\.([^']+)'", (root / 'evidence/axioms.log').read_text())) == len(from_log) == 15
print('All 15 freshly elaborated declarations parsed once and matched the machine record.')
print('Axiom-free, multiline and forbidden-axiom fixtures preserved the reported sets.')
sample = "'CFDLean.sample' depends on axioms: [propext]\n'CFDLean.sample' depends on axioms: [Quot.sound]"
assert parse(sample) == {'sample': {'Quot.sound'}}
print('Duplicate declaration names silently retain the last row. No duplicate occurs in the frozen output.')
