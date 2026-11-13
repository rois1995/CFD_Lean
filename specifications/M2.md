# M2 proposal — original 3D Roe flux

**Status: independently recommended for implementation; awaiting Andrea's scientific approval. No M2 Lean implementation has begun.**

The [proposal review](../reviews/M2/proposal-2264bc0/Review.md) found no blocking mathematical defect in the proposal at `2264bc0`. Its [next-step instructions](../reviews/M2/proposal-2264bc0/START_HERE.md) explicitly reserve scientific approval to Andrea. The original proposal is preserved in Git and the review directory; the following delimiter fixes and implementation clarifications do not supply that approval.

## Proposed numerical flux and caller contract

For admissible left/right conservative states $U_L,U_R\in\mathbb R^5$, a common fixed gas parameter $\gamma>1$, and a face area vector $S\in\mathbb R^3$, propose

\[
\widehat F_\gamma(U_L,U_R,S)=
\begin{cases}
0,&S=0,\\
\tfrac12\bigl(F_\gamma(U_L,S)+F_\gamma(U_R,S)\bigr)
-\tfrac{a}{2}\,D_\gamma(U_L,U_R,n)(U_R-U_L),&S\ne0,
\end{cases}
\qquad a=\sqrt{S\cdot S}=\|S\|_2,\quad n=S/a.
\]

$F_\gamma$ is M1's accepted `physicalFlux`. $D=|\widetilde A_n|$ is the absolute-characteristic-speed operator defined below, **without an entropy correction**. Record arithmetic in this document is componentwise; the flux output has the conserved-vector layout and is not asserted to be an admissible thermodynamic state.

The caller supplies `Conservative 3` states evaluated on the left and right of the same interface point. $S$ points outward from the left control volume toward the right. Its magnitude is face area; $n$ is a dimensionless Euclidean unit normal. Reconstruction, mesh storage, quadrature and incidence belong to later layers. Reversing an oriented interface means swapping states **and** replacing $S$ by $-S$.

Write $U=(\rho,m,\mathcal E)$, $u=m/\rho$, $p=U.\mathrm{pressure}(\gamma)$, and $H=(\mathcal E+p)/\rho$. Energy and momentum in $U$ are per volume; $H$ is specific total enthalpy. $F_n(U):=F_\gamma(U,n)$ is interpreted per unit area. Its components have units of mass, momentum and energy per area per time; multiplying by $a$ gives integrated transfer rates. Normal-Jacobian eigenvalues and the absolute speeds in $D$ have velocity units. The integrated linearization and dissipation are $a\widetilde A_n$ and $aD$. The API must not multiply area twice or use unnormalized $S$ in unit-normal eigenvalue formulae.

Definitions may remain total exact-real expressions, as in M1, with the explicit zero-area branch evaluated without normalizing $S$. Physical claims require the hypotheses below; real division and square root outside this domain have no asserted physical meaning.

## Domain and two-state averages

Common physical hypotheses, denoted **P** below:

- $\gamma>1$, $U_L.\mathrm{Admissible}(\gamma)$, $U_R.\mathrm{Admissible}(\gamma)$.
- For unit-normal statements, $n\cdot n=1$. For the integrated interface, $S$ is arbitrary and the nonzero branch derives this property.

For $K\in\{L,R\}$, set

\[
r_K=\sqrt{\rho_K},\quad w=r_L+r_R,\quad
\theta_K=r_K/w,\quad
\bar u=\theta_Lu_L+\theta_Ru_R,\quad
\bar H=\theta_LH_L+\theta_RH_R,
\]
\[
\bar c^2=(\gamma-1)\left(\bar H-\tfrac12\|\bar u\|^2\right),\qquad
\bar c=\sqrt{\bar c^2},\qquad \bar q=\bar u\cdot n.
\]

P must imply $r_L,r_R,w>0$, $0<\theta_L,\theta_R<1$, and $\theta_L+\theta_R=1$. Prove, rather than assume, the project-derived variance identity

\[
\bar c^2=\theta_Lc_L^2+\theta_Rc_R^2
+\tfrac{\gamma-1}{2}\theta_L\theta_R\|u_R-u_L\|^2>0,
\qquad c_K^2=\gamma p_K/\rho_K>0.
\]

Consequently $\bar c>0$, $\bar c^2\ne0$, $\bar c\ne0$, and all denominators used below are justified. This result concerns the averaged sound speed, not positivity preservation of any time update.

The original matrix construction needs the square-root density **weights**, not an independently selected averaged density. In particular, the density associated with the midpoint of the parameter vector would be $w^2/4$; do not silently substitute the geometric-mean density from a Roe–Pike wave-strength representation. Any later equivalence with that representation requires an explicit theorem.

## Physical Jacobian: an explicit M2 obligation

Use the accepted state fields and an internal coordinate chart

\[
\operatorname{coord}(U)=(\rho,m_x,m_y,m_z,\mathcal E)\in(\mathrm{Fin}\,5\to\mathbb R).
\]

The inverse chart and both round trips are algebraic interface lemmas, not a replacement physical state model. The standard normed space on these finite real coordinates supports a Fréchet-derivative statement. In Lean, the default norm on a finite function space is a supremum norm; it may be used for the derivative topology, but must not be used to define Euclidean face geometry. Geometric lengths and velocity squares use the dot product/`squareSum` from M1. For $S=(2,3,0)$, the required area is $a=\sqrt{13}$ and $n=(2/\sqrt{13},3/\sqrt{13},0)$, so $n\cdot n=1$. In particular, using the default supremum norm would produce area 3 and an invalid unit normal.

For an increment $V=(\delta\rho,\delta m,\delta\mathcal E)$, define a linear operator $J_\gamma(u,H,n)$ by

\[
q=u\cdot n,\quad b=n\cdot\delta m-q\delta\rho,\quad
\delta p=(\gamma-1)\left(\delta\mathcal E-u\cdot\delta m
+\tfrac12\|u\|^2\delta\rho\right),
\]
\[
J_\gamma(u,H,n)V=
\left(n\cdot\delta m,
q\delta m+ub+\delta p\,n,
q(\delta\mathcal E+\delta p)+Hb\right).
\]

For fixed $\gamma,n$, prove that this is the Fréchet derivative of the coordinate representation of $U\mapsto F_\gamma(U,n)$ at every $U$ with $\rho\ne0$, with $u=m/\rho$ and $H=(\mathcal E+p)/\rho$. No density or enthalpy is frozen during differentiation; their variations are already represented by the formula. This differentiability claim does not require $n$ to be unit. The physical domain restricts to $\gamma>1$ and admissible $U$, and its openness should be established for the local continuity arguments. For fixed nonzero $S$, the derivative of the integrated flux is $aJ_\gamma(u,H,n)$; at $S=0$ it is zero.

This is submilestone M2a, not deferred beyond M2. The equal-state matrix identification and Property-U limit statement below depend on it. Merely naming a matrix a Jacobian does not discharge the derivative obligation.

## Original Roe matrix and secant proof

Define the two-state matrix/operator

\[
\widetilde A_n(U_L,U_R)=J_\gamma(\bar u,\bar H,n).
\]

It is constructed from two states, whereas the physical Jacobian is the derivative at one state. The target secant identity is

\[
\widetilde A_n(U_L,U_R)(U_R-U_L)=F_n(U_R)-F_n(U_L).
\]

Multiplying both sides by $a$ gives the integrated identity; its zero-area extension is $0=0$. Also prove symmetry under exchanging the states, equal-state equality with the physical Jacobian, and joint continuity in the admissible state pair for fixed $\gamma,n$. Thus, as both states approach the same admissible $U$, the Roe matrix approaches the physical derivative. Diagonal equality alone will not stand in for the original limiting condition.

Proposed proof route, following Roe's original parameter vector:

\[
z(U)=\sqrt\rho\,(1,u,H),\quad z_*=(z(U_L)+z(U_R))/2.
\]

For $z=(z_0,z_v,z_H)$, the state and unit-normal flux are quadratic maps

\[
\mathcal U(z)=\left(z_0^2,z_0z_v,
\frac{z_0z_H+\tfrac{\gamma-1}{2}\|z_v\|^2}{\gamma}\right),
\]
\[
p(z)=\tfrac{\gamma-1}{\gamma}
\left(z_0z_H-\tfrac12\|z_v\|^2\right),\quad
\mathcal F_n(z)=\bigl(z_0(z_v\cdot n),
z_v(z_v\cdot n)+p(z)n,z_H(z_v\cdot n)\bigr).
\]

First prove the endpoint recovery identities $\mathcal U(z(U_K))=U_K$ and $\mathcal F_n(z(U_K))=F_n(U_K)$ for both admissible states. Let $B=D\mathcal U(z_*)$, $C=D\mathcal F_n(z_*)$. Prove the exact midpoint jump identities $\Delta U=B\Delta z$, $\Delta F=C\Delta z$, invertibility of $B$ from the positive midpoint coordinate $z_0>0$, and $\widetilde A_nB=C$, hence $\widetilde A_n=CB^{-1}$. This yields the secant identity without assuming it. Generalizing the Cartesian construction to arbitrary $n$ and using midpoint derivatives rather than writing every matrix entry are project derivations to prove.

### Source discrepancy requiring approval

Toro 2009, printed p. 355, Eq. (11.57), visibly prints $BC^{-1}$, with $B,C$ as in Eqs. (11.55)–(11.56). The local page was visually inspected, not inferred only from OCR. The jump relations require $CB^{-1}$: Roe 1981 p. 364 explicitly uses that order, and LeVeque p. 320 Eq. (15.27) agrees. $C$ may be singular when a characteristic speed vanishes, so requiring $C^{-1}$ would also improperly exclude valid interfaces.

**Proposed resolution:** follow the original Roe construction and the proved jump identities, using $CB^{-1}$. Record Toro's printed ordering as a suspected typographical error; no author/publisher correction of this equation was located. Andrea's approval is requested explicitly. Do not silently repair the source or treat a suspected erratum as an authenticated publisher correction.

## Eigenstructure and absolute-speed dissipation

Under P and a unit $n$, the acoustic speeds are $\lambda_- =\bar q-\bar c$, $\lambda_+=\bar q+\bar c$, and the convective speed $\lambda_0=\bar q$ has multiplicity three. Proposed eigenvectors/eigenspaces are

\[
r_\pm=(1,\bar u\pm\bar c n,\bar H\pm\bar c\bar q),\qquad
r_c=(1,\bar u,\tfrac12\|\bar u\|^2),
\]
\[
r_t=(0,t,\bar u\cdot t)\quad\text{for }t\cdot n=0.
\]

Prove eigenrelations and completeness: acoustic eigenspaces have dimension one each, and the contact/shear eigenspace has dimension three. The characteristic decomposition must not assume a tangent basis exists with the desired properties without proving its existence/completeness.

**Recommended representation:** avoid choosing a tangent basis in the flux definition. Let $N=\widetilde A_n-\bar qI$. Prove $N^3=\bar c^2N$ and define the spectral projectors

\[
P_-=(N^2-\bar cN)/(2\bar c^2),\quad
P_+=(N^2+\bar cN)/(2\bar c^2),\quad
P_0=I-N^2/\bar c^2.
\]

Prove idempotence, pairwise zero products, sum $I$, eigenspace/rank claims, and

\[
\widetilde A_n=\lambda_-P_-+\lambda_0P_0+\lambda_+P_+,
\qquad
D=|\lambda_-|P_-+|\lambda_0|P_0+|\lambda_+|P_+.
\]

This is a project-derived polynomial representation of the original characteristic dissipation. Prove equivalence to $R\,\mathrm{diag}(|\lambda_i|)R^{-1}$ for every valid complete eigenbasis, including arbitrary choices of the two tangents. These are generally oblique spectral projectors; do not assert Euclidean orthogonality, matrix symmetry, or positive semidefiniteness. The absolute value is spectral, not entrywise absolute value or a singular-value operator.

Orientation obligations: swapping states leaves averages and $D$ unchanged; reversing $n$ negates $\widetilde A_n$, swaps $P_-,P_+$, preserves $P_0$, and leaves $D$ unchanged. These facts, with M1's flux reversal, prove the integrated numerical conservation identity.

## Proposed theorem/acceptance list

This is the separately reviewable list of promised mathematical results. IDs are stable review references, not a target declaration count. Supporting lemmas may be needed; the final implementation must map every ID to qualified Lean declarations and dependencies. No result is proved or approved merely by appearing here.

| ID | Statement and hypotheses | Source or derivation | Role in the discrete path |
| --- | --- | --- | --- |
| M2-J | Coordinate round trips; the explicit $J$ is the Fréchet derivative of the fixed-normal M1 flux on $\rho\ne0$; integrated derivative scales by $a$. | Differentiate accepted M1 definitions; compare Blazek A.7 and Toro (11.47). | Supplies the missing physical Jacobian and anchors the equal-state limit. |
| M2-A | Under P, weights are positive and sum to one; averages are state-symmetric; the displayed variance identity gives $\bar c^2>0$. | Roe/Toro averages plus project algebra and M1 ideal-gas pressure. | Justifies every square root, inverse and eigenvalue separation. |
| M2-R | Under P, exact parameter-vector jump identities and invertible $B$ yield $\widetilde A_n\Delta U=\Delta F_n$; multiply by $a$ for integrated scaling. | Roe (11)–(18), LeVeque (15.26)–(15.27); arbitrary-normal extension derived. | Identifies the actual two-state method and correct wave/flux jumps. |
| M2-L | Under P, diagonal equality with the physical derivative and continuity in the state pair; limits at an admissible equal state agree with $J(U)$. | Roe Property U(ii), LeVeque (15.13); project continuity proof. | Establishes linearization consistency without circular assumptions. |
| M2-E | Under P and unit $n$, prove the displayed eigenrelations, complete 1+3+1 eigenspace split, cubic identity and projector algebra. | Roe (19)–(22), Toro (11.58)–(11.59); arbitrary-normal/projector representation derived. | Makes the dissipation a well-defined operator with the original wave content. |
| M2-D | Under the same hypotheses, the displayed $D$ equals the absolute-speed operator in any complete eigenbasis and is tangent-basis independent. | Toro (11.29), spectral algebra derived. | Prevents a coordinate/basis implementation choice from changing the method. |
| M2-O | Under P, averages are state-symmetric, $\widetilde A_{-n}=-\widetilde A_n$, acoustic projectors swap and $D_{-n}=D_n$. | Project derivation from the explicit formulas. | Provides the signed interface orientation contract consumed by M3. |
| M2-F1 | For admissible $U$, $\gamma>1$, any $S$: $\widehat F(U,U,S)=F_\gamma(U,S)$. | Project derivation from central flux and zero jump. | M3 constant-state/metric-closure argument. |
| M2-F2 | Under P, any $S$: $\widehat F(U_R,U_L,-S)=-\widehat F(U_L,U_R,S)$. | Project derivation from M1 reversal and M2-O. | Interior edge cancellation in M3. |
| M2-F3 | For any raw states/parameter, $\widehat F(U_L,U_R,0)=0$, by the explicit branch; under P, $\widehat F(U_L,U_R,bS)=b\widehat F(U_L,U_R,S)$ for $b\ge0$. | Project zero-area convention and positive scaling derivation. | Degenerate-face handling and correct area scaling. |
| M2-F4 | Under P, $S\ne0$, if $\bar q\ge\bar c$, the flux is $F_\gamma(U_L,S)$; if $\bar q\le-\bar c$, it is $F_\gamma(U_R,S)$. | Original one-sided flux formula, Toro (11.27)–(11.29), secant identity. | Checks full upwinding with Roe characteristic signs. |
| M2-C | The receding-state witness below has admissible endpoints and $\bar c^2>0$, but a negative-density Roe intermediate state. | Explicit project-derived counterexample. | Documents why M5 cannot inherit unconditional positivity. |

All claims use the full domain stated here. In particular, neither the secant identity, completeness, sound-speed positivity nor the desired conservation identity may be inserted as a hypothesis to prove the corresponding promised result. Eigenvalues may vanish; only sound-speed separation is strictly positive. Numerical-flux additivity in arbitrary area vectors is not proposed.

## Examples and limitations

All examples are proposed exact-real checks after approval, alongside general proofs. Embed the following data in three dimensions; omitted velocity/area components are zero. States are formed through M1's primitive conversion.

| Example | Expected fact/value | Obligations exercised |
| --- | --- | --- |
| Equal moving state: $\gamma=2,\rho=2,u=(3,0,0),p=5,S=(4,0,0)$ | $\mathcal E=14$, integrated flux $(24,(92,0,0),228)$. | M2-J, F1, F3; energy/area conventions. |
| Equal oblique state: $\gamma=7/5,\rho=2,u=(3,-1,0),p=5,S=(2,3,0)$ | $\mathcal E=45/2$, flux $(6,(28,9,0),165/2)$. | J, F1, F3; arbitrary-normal handling. |
| Stationary contact: $\gamma=2,p_L=p_R=1,u_L=u_R=0,\rho_L=1,\rho_R=4,S=(1,0,0)$ | $\bar u=0,\bar H=1,\bar c=1$; flux $(0,(1,0,0),0)$. | A, R, E, D; a zero convective eigenvalue must be allowed. |
| Moving contact: same densities/pressures, $u_L=u_R=(1,0,0),S=(2,0,0)$ | $\bar H=3/2,\bar c=1$; flux $(2,(4,0,0),5)$. | R, E, F3, F4; includes a zero acoustic eigenvalue. |
| Stationary shear: $\gamma=2,\rho_L=\rho_R=1,p_L=p_R=1,u_L=(0,1,0),u_R=(0,-1,0),S=(1,0,0)$ | $\bar u=0,\bar c^2=5/2$; flux $(0,(1,0,0),0)$, despite nonzero tangential jump. | A, E, D; repeated convective eigenspace. |
| Swap states and negate area in each two-state case; also set area to zero. | Exactly negative flux; exactly zero flux respectively. | O, F2, F3. |

**Positivity counterexample proposed for M2-C.** Take $\gamma=2$, $\rho_L=\rho_R=1$, $p_L=p_R=1/2$, $u_L=(-2,0,0)$, $u_R=(2,0,0)$, $n=(1,0,0)$. Both endpoint energy densities are $5/2$; both states are admissible. The averages give $\bar u=0,\bar H=3,\bar c=\sqrt3>0$. Define the intermediate state directly by the same projector used in the flux: $U_*=U_L+P_-(U_R-U_L)$. The left acoustic strength in the displayed eigenvector normalization is $-2/\sqrt3$; the projector definition does not depend on that normalization. This intermediate state immediately to the right of the left acoustic wave has

\[
\rho_*=1-2/\sqrt3<0,
\qquad \mathcal E_*=5/2-2\sqrt3.
\]

The strict density sign follows from $0<\sqrt3<2$. This is a counterexample for positivity of the approximate Riemann intermediate state; it is not, by itself, a claim about a particular fully assembled finite-volume update or a CFL bound.

Original Roe dissipation is not asserted to satisfy an entropy inequality or preserve pressure/density under an update. Transonic rarefaction problems are documented in Toro §11.4.1 and Blazek pp. 107–108. No Harten, Harten–Hyman, entropy-stable replacement, clipping, low-Mach modification, carbuncle remedy or positivity fallback is silently included. Each requested variant will need its own definition, authoritative source selection and approval. No entropy-fix source is additionally requested for this unmodified baseline.

## Literature traceability and discrepancy register

All cited items already exist in the approved collection `/media/rausa/4TB/SU2_Versions/Prove/Papers`. Original file identities/hashes remain in references/inventory.json. These are precise locations actually inspected for this proposal; printed page numbers and PDF indices are listed separately because a constant page offset is not reliable across Toro's complete local file.

| Source and locator | Proposed use / convention boundary |
| --- | --- |
| Roe (1981), JCP 43, 357–372, DOI 10.1016/0021-9991(81)90128-5; printed pp. 359–360 (PDF 3–4), Property U(i)–(iv). | Original linearity, limiting consistency, jump and complete-eigenvector requirements. His jump signs may be L−R; our common convention is R−L on both sides. |
| Roe printed pp. 362–363 (PDF 6–7), (10)–(16). | Energy per volume, enthalpy parameter vector, quadratic maps and midpoint jump matrices. His scalar $H$ for enthalpy must not be confused with the Cartesian flux also labelled H. |
| Roe printed pp. 364–365 (PDF 8–9), construction before (17), (19)–(22). | Matrix order $CB^{-1}$, acoustic/convective structure, sound-speed square and wave projection. Original presentation is Cartesian; general normal and basis-free projectors are project derivations. |
| Blazek, first edition 2001, §4.3.3, printed pp. 106–107 (PDF 129–130), (4.84)–(4.90); p. 108 (PDF 131), (4.92). | Cross-check normal Roe jump, averages and flux/dissipation. Read (4.87) with the earlier unit-normal flux convention; area is explicit in our integrated formula. The entropy correction (4.92) is excluded. |
| Blazek Appendix A.7, printed p. 419 (PDF 442), (A.44)–(A.47). | Physical derivative and 3D normal Jacobian. The text includes moving-grid terms $V_t$; set $V_t=0$ for the selected stationary method, not a different moving-grid algorithm. |
| Toro, third edition 2009, DOI 10.1007/b79761, §11.1.2, printed p. 348 (PDF 367), (11.12)–(11.15); §11.1.3 pp. 349–351, especially (11.29) on p. 351 (PDF 370). | Complete hyperbolic eigensystem, diagonal consistency, jump property, original central-plus-absolute-speed flux. We additionally retain Roe's limiting condition explicitly. |
| Toro §11.2.2, printed pp. 354–357 (PDF 373–376), (11.47)–(11.70), especially (11.54)–(11.60). | Physical x-Jacobian, original parameter vector, averages and 3D eigenstructure. Suspected matrix-order error in (11.57) is flagged above. Roe–Pike §11.3 is a distinct construction, not silently substituted. |
| Toro §11.4.1, printed pp. 366–367 (PDF 385–386); §11.4.3 p. 370 (PDF 389), (11.135)–(11.139). | Document entropy limitation and the interpretation of left/right intermediate states. No entropy algorithm is adopted. |
| LeVeque, 2002 print / ©2004 electronic copy, §§15.3.1–15.3.2, printed pp. 315–320 (PDF 337–342), (15.12)–(15.27); §§15.3.4–15.3.5, pp. 322–323 (PDF 344–345), (15.40)–(15.44). | Supporting diagonalizability, limit, jump, matrix-order and 1D average/flux cross-checks. Does not replace Roe's original 3D enthalpy-parameter construction. |

Errata status: no authoritative Blazek first-edition errata list or Toro correction for the inspected matrix-order discrepancy was located. A targeted author/publisher search did not supply one; this does not establish that none exists. The complete [author-maintained LeVeque errata](https://faculty.washington.edu/rjl/book2/errata.html) was checked for the M2 pages. It lists no correction for pp. 315–323 or the cited (15.12)–(15.44). On p. 324 it corrects the intermediate-velocity hat in (15.46), the sign of the second term in (15.47), and the preceding reference to (13.32). Those shallow-water entropy-fix equations are outside the unmodified Euler Roe baseline; they are not imported into this proposal. These observations are a checked errata snapshot, not a guarantee of a complete correction history. No new authoritative reference or different book edition is proposed.

## Proposed implementation sequence and modules — only after approval

| Stage | Planned files / scope | Dependencies and proof difficulty |
| --- | --- | --- |
| M2a | `CFDLean/Core/Coordinates.lean`, `CFDLean/Core/PhysicalJacobian.lean`; coordinate algebra and M2-J. | Reuse M1 state/pressure/physicalFlux. Fréchet derivatives of density divisions, finite-coordinate topology and domain openness are substantive obligations. |
| M2b | `CFDLean/Flux/Roe/Averages.lean`, `Linearization.lean`; M2-A, R, L. | Square-root denominators, the variance identity, midpoint quadratic maps and B invertibility; prove the physical-Jacobian identification, not only a matching formula. |
| M2c | `CFDLean/Flux/Roe/Spectral.lean`; M2-E, D, O. | Cubic/projector algebra, repeated convective eigenspace, complete eigenbasis and basis-independent absolute-speed action. Do not assume spectral conclusions to shorten proofs. |
| M2d | `CFDLean/Flux/Roe/Flux.lean`; M2-F1–F4 and C, examples and public interface. | Explicit zero-area branch, signed reversal, correct area scaling and all-wave upwinding. Reuse the proved linearization and dissipation. |

At the M2a/M2b checkpoint, return an immutable commit, the qualified declaration map for M2-J/A/R/L, the upgraded proof/dependency audit and all unresolved goals. This checkpoint does not authorize M2c results to be assumed.

Only the needed modules are introduced. `CFDLean.lean` exports approved results after their checks pass. Existing M1 mathematical files/contracts remain the accepted baseline. Planned new mathematical modules are solver-independent and retain the approved Lean/mathlib pins unless a separate compatibility decision is justified. No mesh, boundary, time-step or SU2 implementation enters M2.

## Audit upgrade before M2-scale reliance

The existing Python regular-expression inventory is sufficient only for the frozen M1 declaration forms. Before accepting any M2 result:

1. Inventory **fully qualified declarations by owning elaborated project module**, including generated theorems. Record types/kinds, source modules and hashes. Inventory mathematical definitions/types as well as theorem bodies; inspect the transitive constants/axioms of all accepted mathematical roots.
2. Reuse the supplied M1 `KernelInventory.lean` pattern, removing its fixed M1 module/root assumptions for M2. Preserve explicit classification of compiler-generated executable auxiliaries; investigate them and fail if unsafe/unauthorized axioms are reachable from accepted mathematical roots. Do not hide declarations with name filters.
3. Parse audit records under qualified names and **reject duplicates**, including identical duplicates. Add checks for namespace collisions, duplicate rows, multiline and axiom-free records, forbidden axioms and missing promised statements. Never silently retain the last occurrence.
4. Freeze the approved M2 theorem list separately from the implementation, using the IDs above and their qualified declaration map. Fail on missing promised results and unclassified roots. Distinguish audited supporting lemmas from newly claimed scientific contracts; extra names do not confer approval.
5. Retain the accepted foundational set `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, unapproved axiom, concealed unsafe dependency or kernel-bypassing `native_decide` is accepted. Use the nonempty M1 domain and explicit edge cases, not only text scans.
6. Preserve the tested M1 source-only procedure unchanged as historical evidence. For M2, reuse its pinned-source/widget-bootstrap steps and **both** cache controls in a new procedure tied to the new immutable candidate commit. The existing M1 replay script deliberately refuses any other commit. Test the new procedure in a fresh checkout before requesting independent acceptance.

Audit-tool changes, new declarations and changed-proof dependencies must be reviewable. At M2 completion, provide an immutable candidate commit, source hashes, qualified theorem/dependency map, full source-build and axiom evidence, and the unresolved/unsupported-claim list. The independent reviewer supplies acceptance; the worker cannot silently amend the approved contract or self-certify it.

## Route to the composed discrete Euler step

| Milestone | Interface/result consumed next |
| --- | --- |
| M1 — accepted | State conversions, ideal-gas pressure, physical admissibility and oriented physical flux at mathematical revision `0a88e36b3810cd5adc3881db526ca8a35f81afbb`. |
| M2 — this proposal | Two-state integrated numerical flux, physical Jacobian and Roe linearization, consistency and signed reversal. |
| M3 — node-centered assembly | Edge incidence and dual-volume residuals; derive interior cancellation from M2-F2. Distinguish geometric closure assumptions from identities proved for the selected median-dual construction. |
| M4 — stationary boundaries | Approved slip-wall/symmetry discrete contributions; identify and approve a particular far-field variant before using it. Physical requirements and enforcement algorithms remain distinct. |
| M5 — explicit Euler | Update with positive fixed dual volumes; common-step global balance. Unequal local pseudo-time steps weight paired residual contributions differently and require a qualified balance statement. |
| M6 — composition | Compose geometry, interior/boundary residuals and time update into one discrete Euler step with inherited assumptions and a proved global boundary-balance theorem. |

For the common-step case, the intended eventual balance is $\sum_i V_iU_i^{new}=\sum_i V_iU_i-\Delta t\sum_{\text{boundary}}\widehat F_b$, after precise incidence, boundary and fixed-volume hypotheses are approved. This is a later target, not an M2 theorem. The separate SU2 workstream may compare interfaces and import a pinned accepted revision; it must not supply the authoritative CFD definitions.

## Decisions requested from Andrea

1. Approve the opening **original Roe** flux, oriented integrated-area interface, physical domain and explicit zero-area convention, with **no entropy correction or fallback**.
2. Approve the existing source editions and the explicit **$CB^{-1}$** resolution of Toro's printed (11.57), justified by Roe and the exact jump identities. No additional authoritative source is currently requested.
3. Approve the **basis-free polynomial projectors**, with a proof of equivalence to the complete original eigenbasis dissipation, rather than selecting a fixed tangent frame in the interface.
4. Approve the promised result list, including the **physical Fréchet Jacobian**, equal-state limiting consistency, completeness, orientation/area/upwind contracts and the negative intermediate-density witness; approve the M2a–M2d split.
5. Approve the module/coordinate representation and audit upgrade as prerequisites for relying on M2 proofs. Implementation starts only after these statements/choices are approved or amended.

Current verdict: **M1 accepted; M2 proposal awaiting approval.** Blocking for M2 implementation: the decisions above and scientific approval of the recorded source-discrepancy resolution. Nonblocking for M1: the future audit expansion and remaining general errata-history uncertainty. Permitted next action now is scientific review/amendment of this proposal; M2 Lean implementation is not authorized yet.

## Preparation checks and limits

The proposal was checked against the local source pages listed above; Toro p. 355 and Blazek pp. 106–107 were also rendered for visual confirmation. The Blazek text includes the geometric-mean density in its equivalent wave-strength presentation; equivalence to that presentation is not assumed in the original parameter-vector construction. Thirty-six exact-rational state/normal spot checks verified the proposed averaged-sound-speed identity, secant action and cubic operator identity, including the oblique unit normal $(3/5,4/5,0)$. These are preparation checks, not Lean proofs or M2 acceptance. The receding-state endpoints and sound-speed square were checked by exact arithmetic; its negative-density inequality is a mathematical derivation still proposed for kernel verification.

No new Lean source, numerical-flux implementation, proof acceptance, changed source edition or SU2 dependency is part of this proposal.
