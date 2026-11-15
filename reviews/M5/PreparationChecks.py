"""Exact rational M5 proposal checks; no M5 Lean proof or scientific acceptance."""
from fractions import Fraction as F
from pathlib import Path
import runpy

# Reuse the already reviewed preparation evaluator; do not define another Roe solver.
a = runpy.run_path(str(Path(__file__).resolve().parents[1] / 'M4' / 'PreparationChecks.py'))
add, sub, scale = (a[n] for n in ('add', 'sub', 'scale'))
state, physical, wall, roe = (a[n] for n in ('state', 'physical', 'wall', 'roe'))
zero = (F(0),) * 5
vol = {i: F(1, 24) for i in range(4)}


def total(values):
    result = zero
    for value in values:
        result = add(result, value)
    return result


def step(U, R, volumes, dt, used):
    assert all(volumes[i] > 0 for i in used)
    return {i: sub(U[i], scale(dt[i] / volumes[i], R[i])) if i in used else U[i] for i in U}


def amount(U, volumes):
    return total(scale(volumes[i], U[i]) for i in U)


# Actual accepted standard geometry and common-state Roe consistency.
U = {i: a['normal_state'] for i in range(4)}
R = a['assembled'](a['normal_state'], set(range(4)), a['normal_state'])
r = (F(1, 6), F(0), F(0), F(1, 6), F(5, 12))
assert tuple(R[i] for i in range(4)) == (r, zero, zero, scale(-1, r))
assert total(R.values()) == zero
common = {i: F(1, 48) for i in U}
assert amount(step(U, R, vol, common, set(U)), vol) == amount(U, vol)
local = dict(common)
local[3] = F(1, 24)
updated = step(U, R, vol, local, set(U))
assert all(u[0] > 0 and a['pressure'](u) > 0 for u in updated.values())
assert sub(amount(updated, vol), amount(U, vol)) == (F(1, 288), 0, 0, F(1, 288), F(5, 576))
# Actual interior transfers and wall-only boundary transfers with each owner's local step.
f = {e: physical(a['normal_state'], S) for e, S in a['edges'].items()}
g = {b: wall(a['normal_state'], T) for b, T in a['patches'].items()}
edge_term = total(scale(local[i] - local[j], flux) for (i, j), flux in f.items())
boundary_term = total(scale(local[i], flux) for (_, i), flux in g.items())
assert sub(amount(updated, vol), amount(U, vol)) == scale(-1, add(edge_term, boundary_term))
print('Common-step balance and exact unequal-step edge/boundary formula pass on accepted standard geometry.')
print('Unequal-step all-wall amount change = (1/288,0,0,1/288,5/576); initial and updated states are admissible.')

# A zero-volume unused allocated node is held without evaluating a quotient.
U[4] = a['rest']; R[4] = zero; vol[4] = F(0); common[4] = F(7)
assert step(U, R, vol, common, set(range(4)))[4] == U[4]
try:
    step(U, R, vol, common, set(U))
except AssertionError:
    pass
else:
    raise AssertionError('A used zero-volume node must be rejected')
assert step(U, R, vol, {i: F(0) for i in U}, set(range(4))) == U
assert step(U, {i: zero for i in U}, vol, common, set(range(4))) == U
print('Zero-step/zero-residual identity, unused zero-volume hold and used zero-volume exclusion pass.')

# An actual compatible common-state residual gives unchanged states at every local step.
for value, faces in [(a['tangent'], {3}), (a['rest'], set(range(4)))]:
    states = {i: value for i in range(4)}
    residual = a['assembled'](value, faces, value)
    assert step(states, residual, {i: F(1, 24) for i in states}, local, set(states)) == states
print('Actual mixed-wall tangent and all-wall rest common states remain unchanged for unequal steps.')

# Admissible hot owner/rest wall, cold exterior on only actual face 1: no unconditional update positivity.
hot = state(F(1), a['Z'], F(3)); cold = a['rest']
residual = {i: zero for i in range(4)}
for (i, j), S in a['edges'].items():
    flux = physical(hot, S)
    residual[i] = add(residual[i], flux); residual[j] = sub(residual[j], flux)
for (face, i), T in a['patches'].items():
    flux = wall(hot, T) if face == 3 else roe(hot, cold, T) if face == 1 else physical(hot, T)
    residual[i] = add(residual[i], flux)
assert residual[0] == (F(1, 12), F(1, 6), 0, 0, F(1, 3))
large = step({i: hot for i in range(4)}, residual, {i: F(1, 24) for i in range(4)}, {i: F(1) for i in range(4)}, set(range(4)))
assert large[0] == (-1, -4, 0, 0, -5)
print('Actual admissible hot/cold prescribed-face example at dt=1 gives owner state (-1,-4,0,0,-5).')
print('These are exact proposal feasibility checks, not Lean proofs, CFL bounds or positivity/accuracy claims.')
