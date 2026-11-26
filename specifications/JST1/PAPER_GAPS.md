# Paper gaps found by the Lean work (paper1.tex, frozen copy of 2026-11-24)

Status of each gap: OPEN (paper not changed yet), FIXED (paper changed), REJECTED.
All four FIXED in `Handbook/paper1/paper1.tex` sha256 32e1f260… (2026-11-25 13:54), checked by diff.
Answers marked "solver session" came from the numerical-development session through the user on 2026-11-25. They are
proposed answers; the paper session must check them against the text.

## G1. `lem:eps2` (lines 253, 268): "both bounds are sharp" — FIXED (2026-11-25)

- What is missing: the proof shows equality only for the pointwise quadratic forms (eigenvectors of the pencil).
  For two real states the ratio [w]·[ũ] / [w]·[u] probably never equals λ_γ or Λ_γ. "Sharp" is true only as
  "best constants".
- Solver session: agrees. Change "sharp" to "best constants" (no smaller lower constant and no larger upper constant
  holds for all states). Add one line to the proof: the ratio tends to the bound when the two states come close to
  each other along the worst direction.
- Lean: P1-1.6 is this best-constant statement (for every ε > 0 there is an admissible pair with ratio within ε of
  the bound).
- Side note (not a gap): the reduction to v = 0 (Galilean invariance, line 262) is not needed. The forms q and q̃ of
  lines 264-265 hold for any velocity (checked with sympy).

## G2. `lem:splitmean` (lines 587-601): closure (A) and the sensor ratio — FIXED (2026-11-25)

- What is missing: (A) says "every nodal quantity is replaced by its mean over the splits". The sensor ς_i is a
  ratio of two sums. The mean of the ratios is not the ratio of the means, so (A) as written does not give
  eq. (splitmean) for ς_i.
- Solver session: the method computes the sensor and the counts on the π-weighted pair graph (numerator and
  denominator are π-weighted sums; the ratio comes after). Fix: (A) applies only to the parts that are linear in the
  split shares (sums, Laplacians). The sensor is defined from the weighted sums; it is not a mean of split sensors.
- Lean: the sensor (hence ε2, ε4) is a fixed, split-independent input. P1-3.2 proves the exact means of the linear
  sums; the ratio is taken after.
- Code check (paper session, 2026-11-25): the code agrees. It adds π_ik(s_k − s_i) and π_ik(s_k + s_i) to the two
  sums and takes the ratio after that (`SU2_CFD/include/solvers/CFVMFlowSolverBase.hpp`, comment at line 512). The
  sensor is not a mean of split sensors. The Lean model matches the code; no statement change.

## G3. `lem:splitmean`: the boundary part of Λ_i under a split — FIXED (2026-11-25)

- What is missing: Λ_i contains a sum over the boundary faces of i. The paper does not say how this sum is treated
  in a split (each split has its own boundary normals on quadrilateral boundary faces).
- Solver session: the paper session reads the code and writes the same rule into the paper ("share 1" if the term is
  split-independent, else the mean over the splits).
- Lean: the boundary term is a given non-negative input `bnd i`, the same for all splits, until the paper says more.
- Code check (paper session, 2026-11-25): the rule is "share 1". The boundary term uses the median-dual normal of the
  boundary vertex, which does not change with a split (`CFVMFlowSolverBase.hpp:861-895`). The boundary sum skips
  Euler walls, symmetry planes, internal, near-field and periodic markers; the paper must say this too. The split
  pairs enter Λ in a separate step (`AddSplitPairNodalLambda`, line 494): each pair adds |ū·n_ik| + c̄|n_ik| on the
  full coefficient n_ik, which already contains π_ik. Inner edges use the form normal (`GetFormNormal`).
- Lean match: `LamOn` is Σ_k (|v̄·n_ik| + c̄|n_ik|) + `bnd i` on the π-inclusive coefficient n_ik, and P1-3.1 proves
  that the mean over the splits gives exactly this. The skipped markers only change what `bnd i` is; `bnd i` is a
  free non-negative input, so the statement covers it. No statement change.

## G4. `lem:splitmean`: positivity hypotheses — FIXED (2026-11-25)

- What is missing: the proof divides by π_ik, λ̂_ik and Λ_i and uses (π x)^a = π^a x^a. It needs π_ik > 0,
  λ̂_ik > 0 and Λ_i > 0 (and Λ_k > 0). The paper does not state them.
- Solver session: add before the lemma "We assume admissible states and a valid mesh, so π, λ̂ and Λ_i are positive."
  π > 0 follows if the pair graph contains only pairs with π > 0; λ̂ > 0 follows from c̄ > 0 and n_ik ≠ 0.
- Lean: all of them are explicit hypotheses of P1-3.1 and P1-3.3.

## Paper changes of 2026-11-25 (solver session)

Live copy changed: `SU2_NativeIntegrated/Handbook/paper1/paper1.tex` (backup `paper1.tex.bak_20261125_gaps`). The frozen
copy `LEAN_HANDOFF_PAPER1/paper1.tex` is not changed. pdflatex compiles with no error.

- G1: the lemma says "best constants" (no larger lower constant and no smaller upper constant holds for all admissible
  pairs). The proof adds: the ratio tends to the eigenvalue when u_k tends to u_i along its eigenvector; for two
  distinct states the ratio is in general strictly inside. (The file above had the directions swapped: the best lower
  constant is the largest one.)
- G2: (A) now applies only to the quantities linear in the pair indicator (counts, L_i, sensor numerator and
  denominator). The sensor is the ratio of the two mean sums, not the mean of split sensors. The proof says the same.
- G3: the lemma says the boundary part of Λ_i is unchanged (share 1; A_{f,i} is the same in every split). The Λ_i
  definition says slip walls, symmetry planes and periodic boundaries add no term. (Internal and near-field markers are
  not used in the paper.)
- G4: before the lemma: π_ik > 0 on the pair graph, λ̂_ik > 0 (c̄ > 0 and ν_ik ≠ 0), Λ_i > 0. Note: λ̂ uses the edge
  projection ν_ik, so the needed condition is ν_ik ≠ 0, not only n_ik ≠ 0. The Lean hypothesis on λ̂ > 0 covers it.

## P4 (2026-11-26): gaps found by the P4 statement review (paper not changed; the paper session decides)

### G5. `prop:wallJST`(ii): "removes only dissipative second-difference terms" — OPEN

- The cut sets ε2 = ε4 = 0 on the wall-crossing edges, so it also removes the fourth-difference terms (whose
  production has no sign in general and is ≥ 0 in the model of (iii)). The conclusion ("every identity and inequality
  ... holds unchanged") stays right, since those results hold for any ε4 ≥ 0, including 0.
- Suggested wording: "removes the fourth-difference terms (no entropy sign is used for them) and dissipative
  second-difference terms, whose production is ≤ 0 edge by edge".
- Lean: P4-15.4 splits both Π^(2) and Π^(4) exactly; no statement change needed.

### G6. `prop:consistency`(b): smoothness of F^ec — OPEN

- "F^ec differs from the mean by O(|u_k - u_i|²)" needs F^ec to be C² near the diagonal. The proof says "a symmetric,
  consistent, smooth two-point flux". For the Ismail-Roe flux this is the smoothness of the logarithmic mean across
  a = b (true, e.g. 1/L(a, b) = ∫_0^1 dt/((1-t)a + tb), but not argued).
- Lean: P4-16.2 is the abstract statement; the instance for `ismailRoe` (piecewise `logMean`) is not stated.
- P5 (2026-11-26): the instance is proved (Lean side closed; the paper text is still OPEN). P5-19.1: `logMean` is Cⁿ
  for all n on (0, ∞)² (`L(a, b) = a (e^t - 1)/t`, `t = ln b - ln a`). P5-19.2: the Ismail-Roe flux is Cⁿ on
  admissible × admissible. P5-19.3: `|F^IR - mean| ≤ C|y||u_k - u_i|²` near each admissible diagonal point.
  Suggested wording: "the Ismail-Roe flux is smooth near the diagonal, since 1/L(a, b) = ∫_0^1 dt/((1-t)a + tb)".
  Further notes of the P5 reviewer: the constant is only locally uniform (states in a compact subset of the admissible
  set; it scales with |n_ik|); "expand about the midpoint" needs the segment [u_i, u_k] admissible (true: the
  admissible set is convex in conservative variables).

### G7. `prop:wallJST` spectrum proof (cosmetic) — OPEN

- "a product of a positive semidefinite and a positive definite matrix (or G_II² on a component without wall
  neighbours)": the case split is per connected component; "the product of two positive semidefinite matrices has a
  real non-negative spectrum" covers all cases at once (this is the Lean proof of P4-15.6). G_II is the
  negative-semidefinite (L_i = Σ(u_k - u_i)) Laplacian; saying so would help the reader.

## Paper change during P5/P6 (2026-11-26 10:23)

`paper1.tex` sha256 changed `32e1f260…` -> `5ec5f9db…` (backup of the old copy: `paper1.tex.bak_20261126_figs`). The
diff touches only the numerical-results section (figures of the final campaign, ONERA M6 text and table, a stated
limitation of the scheme on the mixed M6 mesh in the inviscid case). No definition, statement or proof changed, so no
frozen Lean statement is affected; line numbers after the results section moved (e.g. `∫_T φ_i = m_T`: line 975).

## P6 (2026-11-26): notes of the P6 statement review (paper not changed; the paper session decides)

- `prop:consistency`(b) on mixed meshes: `∫_Ω φ_i ∇·F_h` has no single integrand there (φ_i and F_h depend on the
  split); "the same holds split by split" should say the integral is the ω_s-weighted sum over the sub-simplices
  (P6-21.3 states it so).
- The proof uses "interior vertex" in the algebraic sense (Σ_k n_ik = 0, B_ik = 0), which on mixed meshes rests on
  `lem:avg`.
- Cosmetic: the setting asks W_a^T > 0, mixed meshes allow ω_s ≥ 0.
