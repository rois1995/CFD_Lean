"""Generate catalog/README.md from catalog/theorems.json (MC-C theorem catalog).

Usage: python3 scripts/catalog.py          (rewrite catalog/README.md)
       python3 scripts/catalog.py --check  (exit 1 if catalog/README.md is not the generated text)
The output depends only on the JSON, so it is deterministic; scripts/verify.py compares it byte for byte.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATALOG = "catalog/theorems.json"
README = "catalog/README.md"
LAYERS = ("Foundations", "Geometry", "Discrete operators", "Entropy framework", "Physics models", "Schemes", "Time",
          "Execution")
MILESTONES = ("M1", "M2", "M3", "M4", "M5", "MC-N", "B0", "B1", "B2", "B3", "B4", "E0", "E0b", "B3b", "E0c", "JST1")
STATUSES = ("accepted", "pending", "candidate")
METHOD_SETS = (("FEM",), ("FVM",), ("FEM", "FVM"), ("method-free",))

RULES = """\
## Rules

Each entry of `theorems.json` is one promised theorem: the 15 accepted M1 theorems (M1 has no result map; its
accepted list is the `#print axioms` list of the hash-pinned `Integrity.lean`, with IDs `M1-1`..`M1-6` for the
targets of `specifications/M1.md` and `M1-aux` for the finite-sum lemmas), every declaration bound in
`specifications/M2-results.json` .. `M5-results.json`, every theorem of `specifications/MC-N-results.json`, and the
121 paper-1 proofs bound in `specifications/JST1/P1-results.json` .. `P8-results.json` (IDs `P1-x.y` .. `P8-x.y`).

**Status.** `accepted`: M1-M4, independently accepted (`reviews/*/Acceptance.md`). `pending`: M5, implemented,
independent review pending. `candidate`: MC-N, moved from JST_Paper_Lean on branch `mc-n`, not yet merged to `main`;
JST1, the paper-1 statements folded from JST_Paper_Lean by MR-2 and the P4-P8 statements written here (self-checked,
AI-reviewed, not independently accepted). The 37 JST1 proofs whose statement is an MC-N theorem delegate to it and carry its layer, tags and summary.

**Layer** (by the mathematical object a statement is about, not by milestone or module):

| Layer | Content |
|---|---|
| Foundations | Generic algebra and analysis: sums of squares, dot products, state coordinates, unit normals, log mean. |
| Geometry | Simplices and meshes: P1 simplex calculus, facet vectors, median-dual flags, interfaces, patches, volumes, boundary records, used nodes, facet/side balance, pulling splits of mixed cells. |
| Discrete operators | Mesh operators independent of the flux function: edge incidence and assembly, P1/SBP operators (c, B, beta, defect), Galerkin and finite-volume residual identities, edge dissipation tensors. |
| Entropy framework | Entropy production and conservation identities of pair fluxes and boundary closures. |
| Physics models | Ideal-gas Euler states, admissibility, entropy variables, physical flux and Jacobian, Roe averages, linearization and eigenstructure; the Navier-Stokes viscous matrix, wall conditions and the SST model. |
| Schemes | Numerical fluxes and their residuals: Roe flux, Roe edge/boundary transfers, boundary kinds, closures, residual balances, constant-state and free-stream consistency, JST dissipation coefficients, viscous and wall element terms, entropy bounds of the complete scheme. |
| Time | The explicit Euler update, amounts, conservation balances and step controls. |
| Execution | Executable array kernels and their refinement to the mathematical schemes (Burgers E0, E0b, E0c). |

**Method tags** (`FEM`, `FVM`, both, or `method-free`):

- `FEM`: statements about Galerkin / P1-basis / SBP-operator objects (Galerkin residual, `c_ik`, boundary matrix `B`,
  `beta_i`, closed vertices of the P1 operator). Tagged `FEM` and `FVM` when the statement also involves the
  finite-volume side: an FV <-> Galerkin equivalence, dual edge normals `n_ik`, or median-dual facets.
- `FVM`: median-dual geometry (flags, interfaces, patches, dual volumes, boundary records), interface/edge fluxes
  and edge dissipation, assembly and incidence, boundary transfers and closures, residual balances, and the time
  update on dual volumes.
- `method-free`: pure algebra/analysis of states, fluxes, the Roe matrix, the log mean, single-simplex calculus,
  primal-mesh combinatorics and facet/side balance, entropy-production calculus, and the pointwise Euler step.
- Entropy statements about one pair of states (a pair flux, its production) are `method-free`; sums over the nodes or
  pairs of a mesh, or semi-discrete rates over dual volumes `V_i`, are `FVM`.

**Burgers** (milestones `B0` .. `B4`, `B3b`, `E0`, `E0b`, `E0c`, status `pending`: implemented, independent review pending). The declarations
bound in `specifications/Burgers-B0-results.json` .. `Burgers-B4-results.json`, `Burgers-B3b-results.json`, `Burgers-E0-results.json`, `Burgers-E0b-results.json` and `Burgers-E0c-results.json`: the scalar two-point-flux finite-volume
core on a periodic grid, the incremental-form stability lemmas, the convexity of bounded states and of the total
variation, the MUSCL reconstruction with a limiter certificate (Discrete operators), the flux certificates and the
Burgers Rusanov flux (Schemes), the Forward Euler step, its stability under a CFL hypothesis, the generic SSP
Runge-Kutta composition and the multi-step results (Time), the entropy certificates of a two-point flux and the
semidiscrete entropy inequalities (Entropy framework), the refinement of the executable array kernel (Execution). `FVM` marks the periodic finite-volume statements; the
generic time-stepping statements are `method-free`.

**Source.** The contract or result map and the result ID (with stage, or the JST statement for MC-N and JST1).

Generated by `python3 scripts/catalog.py` from `theorems.json`; `scripts/verify.py` checks coverage, tag values and
that this file equals the generated text. Do not edit by hand.
"""


def cell(text):
    return text.replace("|", "\\|")


def method_label(methods):
    return " + ".join(methods)


def render(record):
    entries = record["theorems"]
    lines = ["# CFD_Lean theorem catalog (MC-C)", "",
             f"{len(entries)} promised theorems, grouped by layer.", "", RULES]
    lines += ["## Counts", "", "| Layer | Theorems | " + " | ".join(map(method_label, METHOD_SETS)) + " |",
              "|---|---:|" + "---:|" * len(METHOD_SETS)]
    for layer in LAYERS:
        group = [e for e in entries if e["layer"] == layer]
        counts = [sum(tuple(e["methods"]) == m for e in group) for m in METHOD_SETS]
        lines.append(f"| {layer} | {len(group)} | " + " | ".join(map(str, counts)) + " |")
    totals = [sum(tuple(e["methods"]) == m for e in entries) for m in METHOD_SETS]
    lines.append(f"| **Total** | {len(entries)} | " + " | ".join(map(str, totals)) + " |")
    lines += ["", "| Method tag | Theorems carrying it |", "|---|---:|"]
    for tag in ("FEM", "FVM", "method-free"):
        lines.append(f"| {tag} | {sum(tag in e['methods'] for e in entries)} |")
    lines += ["", "| Milestone | Status | Theorems |", "|---|---|---:|"]
    for milestone in MILESTONES:
        group = [e for e in entries if e["milestone"] == milestone]
        status = ", ".join(sorted({e["status"] for e in group}))
        lines.append(f"| {milestone} | {status} | {len(group)} |")
    for layer in LAYERS:
        group = [e for e in entries if e["layer"] == layer]
        lines += ["", f"## {layer} ({len(group)})", "", "| Theorem | ID | Methods | Status | Summary |",
                  "|---|---|---|---|---|"]
        for e in group:
            lines.append(f"| `{e['name']}` | {e['id']} | {method_label(e['methods'])} | {e['status']} | "
                         f"{cell(e['summary'])} |")
    return "\n".join(lines) + "\n"


def main(argv):
    text = render(json.loads((ROOT / CATALOG).read_text(encoding="utf-8")))
    target = ROOT / README
    if argv[1:] == ["--check"]:
        if not target.exists() or target.read_text(encoding="utf-8") != text:
            print(f"{README} is not the output of scripts/catalog.py")
            return 1
        return 0
    if argv[1:]:
        print(__doc__)
        return 2
    target.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
