# P6 statement review (item 21)

Independent reviewer: one fresh agent (Opus, high effort), 2026-11-26. It received the paper lines (P1 operator and
`m_T`, `prop:consistency`, its proof, mixed meshes), the statement file `Spec/Item21.lean` and the definitions it uses
(`bary`, `p1Interp`, `Simplex`, `WMesh`), but not the author's opinion. Read-only review; two `lake env lean` runs on a
scratch copy: `divP1` equals `Σ_β Σ_b g_bβ F_bcβ` (so `deriv` never falls back to 0), `P6_21_2 → P6_21_3` in about 20
lines on top of P4-16.1 (so 21.3 is not true for a wrong reason), and `volume univ = 1` on `Fin 0 → ℝ` (d = 0).

**Verdict: no BLOCKING finding**; all three statements true, faithful, non-vacuous; no name capture.

## Findings and follow-up

| # | Severity | Finding | Follow-up (before freeze) |
|---|---|---|---|
| 1 | minor | 21.3's right side is the weighted cell sum, not a literal `∫_Ω`; they agree on a conforming simplex mesh (no conformity predicate in `WMesh`); on mixed meshes the cell sum is the only meaning. | Docstring says so. |
| 2 | minor | 21.3 is a corollary of 21.2 and P4-16.1. | Docstring says so; the proof is the reviewer's sketch. |
| 3 | minor | `divP1` uses coordinate-line derivatives, not the trace of `fderiv`; equal here. | Accepted. |
| 4 | minor | The paper changed during the session (sha256 now `5ec5f9db…`, was `32e1f260…`); the sentence is now at line 975. | Header updated; the diff touches only the numerical-results section (figures, ONERA M6 table), no statement or proof (`PAPER_GAPS.md`). |
| 5 | minor | 21.2 also serves the uses of `∫_T φ_a = m_T` at lines 915 and 1025. | Header cites them. |

Paper notes of the reviewer (recorded in `PAPER_GAPS.md`, P6 section): on mixed meshes `∫_Ω φ_i ∇·F_h` has no single
global integrand (φ_i and F_h depend on the split); "interior vertex" is used in the algebraic sense (`B_ik = 0`);
`W_a^T > 0` in the setting vs `ω_s ≥ 0` on mixed meshes (harmless).
