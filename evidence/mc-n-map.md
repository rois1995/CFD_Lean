# MC-N statement map: JST_Paper_Lean → CFDLean.Num

Source: JST_Paper_Lean branch `v436`, commit `afdf4f9b4f98f089af82074bf7e4db99177844ad` (statement text from its `evidence/statements-v4.36.txt` and `evidence/statements-raw-v4.36.txt`). CFD types printed by `scripts/MCNStatementDump.lean` with the same settings as JST `scripts/DumpStmts.lean` (`STMT`, `pp.fullNames`) and `scripts/DumpStmtsRaw.lean` (`XSTMT`, no notation, no coercions, `pp.funBinderTypes`); output in `evidence/mc-n-statements.log`. Result bindings: `specifications/MC-N-results.json`.

Comparison rule: rename the constants `NumCore.*` → `CFDLean.Num.*`, `Paper1.Spec.*` → `CFDLean.Num.*`, `Paper1.*` → `CFDLean.Num.*` in the JST text, collapse whitespace (line breaks move because the names are longer), and compare with the CFD text. Each CFD theorem is stated directly (no `Prop` wrapper): its type is the body of the JST `Prop`.

Result: 37 of 37 identical in the pretty dump, 37 of 37 identical in the raw dump. No statement differs beyond the namespace of its constants.

| ID | JST statement | CFD theorem | Module | pretty = | raw = | Note |
|---|---|---|---|---|---|---|
| MC-N.P1-2.4 | `Paper1.Spec.P1_2_4` | `CFDLean.Num.logMean_properties` | `CFDLean.Num.LogMean` | yes | yes | namespace only |
| MC-N.P1-5.1 | `Paper1.Spec.P1_5_1` | `CFDLean.Num.Simplex.calculus` | `CFDLean.Num.Simplex` | yes | yes | namespace only |
| MC-N.P3-11.2 | `Paper1.Spec.P3_11_2` | `CFDLean.Num.Simplex.facet_cross3` | `CFDLean.Num.Simplex` | yes | yes | `Paper1.Spec.cross3` is now `CFDLean.Num.cross3` (definition moved verbatim). |
| MC-N.P3-11.2b | `Paper1.Spec.P3_11_2b` | `CFDLean.Num.Simplex.facet_perp2` | `CFDLean.Num.Simplex` | yes | yes | `Paper1.Spec.perp2` is now `CFDLean.Num.perp2` (definition moved verbatim). |
| MC-N.P3-12.5 | `Paper1.Spec.P3_12_5` | `CFDLean.Num.pathSimplex_nonobtuse` | `CFDLean.Num.Simplex` | yes | yes | `Paper1.Spec.pathSimplex` is now `CFDLean.Num.pathSimplex` (definition moved verbatim). |
| MC-N.P1-2.3 | `Paper1.Spec.P1_2_3` | `CFDLean.Num.WMesh.nW_row_sum` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P2-6.1 | `Paper1.Spec.P2_6_1` | `CFDLean.Num.WMesh.sbp_defect` | `CFDLean.Num.Mesh` | yes | yes | Uses `CFDLean.Num.WMesh.EW` (JST `NumCore.WMesh.EW`); the definition moved from JST `NumCore/Boundary.lean` to `CFDLean/Num/Mesh.lean`, text unchanged. |
| MC-N.P2-6.2 | `Paper1.Spec.P2_6_2` | `CFDLean.Num.Simplex.median_defect_iff` | `CFDLean.Num.Mesh` | yes | yes | Simplex statement placed in module `Mesh` (MC-N.md lists it there). |
| MC-N.P1-5.2 | `Paper1.Spec.P1_5_2` | `CFDLean.Num.WMesh.dissGeom_edge` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P1-5.3 | `Paper1.Spec.P1_5_3` | `CFDLean.Num.WMesh.dissGeom_outer` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P1-5.4 | `Paper1.Spec.P1_5_4` | `CFDLean.Num.WMesh.dissGeom_calibration` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P2-7.1 | `Paper1.Spec.P2_7_1` | `CFDLean.Num.quadratic_edge_expansion` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P2-7.2 | `Paper1.Spec.P2_7_2` | `CFDLean.Num.dissTensor_loewner` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P2-7.3 | `Paper1.Spec.P2_7_3` | `CFDLean.Num.WMesh.dissTensor_trace` | `CFDLean.Num.Mesh` | yes | yes | namespace only |
| MC-N.P1-5.0a | `Paper1.Spec.P1_5_0a` | `CFDLean.Num.WMesh.closed_of_facetPaired` | `CFDLean.Num.Boundary` | yes | yes | namespace only |
| MC-N.P2-6.3 | `Paper1.Spec.P2_6_3` | `CFDLean.Num.WMesh.conforming_boundary` | `CFDLean.Num.Boundary` | yes | yes | namespace only |
| MC-N.P3-11.1 | `Paper1.Spec.P3_11_1` | `CFDLean.Num.WMesh.facetBalanced_boundary` | `CFDLean.Num.Boundary` | yes | yes | namespace only |
| MC-N.P3-11.4 | `Paper1.Spec.P3_11_4` | `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced` | `CFDLean.Num.Boundary` | yes | yes | `Paper1.Spec.SideBalanced` (and `facetSide`, `cross3`) are now in `CFDLean.Num` (definitions moved verbatim). |
| MC-N.P3-11.4b | `Paper1.Spec.P3_11_4b` | `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2` | `CFDLean.Num.Boundary` | yes | yes | `Paper1.Spec.SideBalanced2` (and `facetSide2`, `perp2`) are now in `CFDLean.Num` (definitions moved verbatim). |
| MC-N.P1-2.1 | `Paper1.Spec.P1_2_1` | `CFDLean.Num.antisymmetric_pairFlux` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P1-2.2 | `Paper1.Spec.P1_2_2` | `CFDLean.Num.entropyConservative_production` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P1-2.6 | `Paper1.Spec.P1_2_6` | `CFDLean.Num.dissipativePairFlux_conservation` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P1-2.7 | `Paper1.Spec.P1_2_7` | `CFDLean.Num.dissipativePairFlux_freeStream` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P2-6.4 | `Paper1.Spec.P2_6_4` | `CFDLean.Num.edgeForm_boundary_split` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P2-6.5 | `Paper1.Spec.P2_6_5` | `CFDLean.Num.WMesh.standardClosure_entropy` | `CFDLean.Num.PairFlux` | yes | yes | `Paper1.Spec.stdWeight` is now `CFDLean.Num.stdWeight` (definition moved verbatim). |
| MC-N.P2-6.5b | `Paper1.Spec.P2_6_5b` | `CFDLean.Num.WMesh.standardClosure_linear` | `CFDLean.Num.PairFlux` | yes | yes | `Paper1.Spec.stdWeight` is now `CFDLean.Num.stdWeight` (definition moved verbatim). |
| MC-N.P2-8.1 | `Paper1.Spec.P2_8_1` | `CFDLean.Num.quadratureClosure_entropy` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P2-8.2 | `Paper1.Spec.P2_8_2` | `CFDLean.Num.quadratureClosure_freeStream` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P2-8.3 | `Paper1.Spec.P2_8_3` | `CFDLean.Num.quadratureClosure_linear` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P2-8.4 | `Paper1.Spec.P2_8_4` | `CFDLean.Num.WMesh.faceRule_beta_B` | `CFDLean.Num.PairFlux` | yes | yes | namespace only |
| MC-N.P1-4.1 | `Paper1.Spec.P1_4_1` | `CFDLean.Num.WMesh.galerkin_identity` | `CFDLean.Num.Galerkin` | yes | yes | namespace only |
| MC-N.P1-5.5 | `Paper1.Spec.P1_5_5` | `CFDLean.Num.WMesh.fvRes_eq_galerkinRes` | `CFDLean.Num.Galerkin` | yes | yes | namespace only |
| MC-N.P2-6.7 | `Paper1.Spec.P2_6_7` | `CFDLean.Num.WMesh.closed_mean_galerkin` | `CFDLean.Num.Galerkin` | yes | yes | namespace only |
| MC-N.P3-13.1 | `Paper1.Spec.P3_13_1` | `CFDLean.Num.pair_production_integral` | `CFDLean.Num.Production` | yes | yes | namespace only |
| MC-N.P1-5.0b | `Paper1.Spec.P1_5_0b` | `CFDLean.Num.ofMeshData_closed` | `CFDLean.Num.Bridge` | yes | yes | `Paper1.ofMeshData` is now `CFDLean.Num.ofMeshData` (definition moved verbatim). |
| MC-N.P1-5.6 | `Paper1.Spec.P1_5_6` | `CFDLean.Num.dualFacets_grad` | `CFDLean.Num.Bridge` | yes | yes | `Paper1.simplexOfPoints`, `Paper1.dualFacet2` are now in `CFDLean.Num` (definitions moved verbatim; `dualFacet2`, `rot90` in module `Simplex`). |
| MC-N.P1-5.7 | `Paper1.Spec.P1_5_7` | `CFDLean.Num.ofMeshData_fv_galerkin` | `CFDLean.Num.Bridge` | yes | yes | `Paper1.ofMeshData` is now `CFDLean.Num.ofMeshData` (definition moved verbatim). |

## Statements

### MC-N.P1-2.4: `CFDLean.Num.logMean_properties`

JST `Paper1.Spec.P1_2_4` (proof `Paper1.Proofs.p1_2_4`):

```lean
∀ (a b : ℝ),
  0 < a →
    0 < b →
      NumCore.logMean a b = NumCore.logMean b a ∧
        NumCore.logMean a a = a ∧ 0 < NumCore.logMean a b ∧ b - a = NumCore.logMean a b * (Real.log b - Real.log a)
```

CFD `CFDLean.Num.logMean_properties` (module `CFDLean.Num.LogMean`):

```lean
∀ (a b : ℝ),
  0 < a →
    0 < b →
      CFDLean.Num.logMean a b = CFDLean.Num.logMean b a ∧
        CFDLean.Num.logMean a a = a ∧
          0 < CFDLean.Num.logMean a b ∧ b - a = CFDLean.Num.logMean a b * (Real.log b - Real.log a)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.1: `CFDLean.Num.Simplex.calculus`

JST `Paper1.Spec.P1_5_1` (proof `Paper1.Proofs.p1_5_1`):

```lean
∀ (d : ℕ) (T : NumCore.Simplex d),
  T.Nondeg →
    ∑ a, T.grad a = 0 ∧
      (∀ (a b c : Fin (d + 1)),
          NumCore.dot (T.grad a) (T.x b - T.x c) = (if a = b then 1 else 0) - if a = c then 1 else 0) ∧
        ∑ a, NumCore.outer (T.grad a) (T.x a) = 1 ∧ 0 < T.vol ∧ ∑ o, T.facet o = 0
```

CFD `CFDLean.Num.Simplex.calculus` (module `CFDLean.Num.Simplex`):

```lean
∀ (d : ℕ) (T : CFDLean.Num.Simplex d),
  T.Nondeg →
    ∑ a, T.grad a = 0 ∧
      (∀ (a b c : Fin (d + 1)),
          CFDLean.Num.dot (T.grad a) (T.x b - T.x c) = (if a = b then 1 else 0) - if a = c then 1 else 0) ∧
        ∑ a, CFDLean.Num.outer (T.grad a) (T.x a) = 1 ∧ 0 < T.vol ∧ ∑ o, T.facet o = 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-11.2: `CFDLean.Num.Simplex.facet_cross3`

JST `Paper1.Spec.P3_11_2` (proof `Paper1.Proofs.p3_11_2`):

```lean
(∀ (T : NumCore.Simplex 3) (o a b c : Fin 4),
    T.Nondeg →
      [o, a, b, c].Nodup →
        let nv := Paper1.Spec.cross3 (T.x b - T.x a) (T.x c - T.x a);
        T.facet o = (if 0 < NumCore.dot nv (T.x o - T.x a) then -(1 / 2) else 1 / 2) • nv) ∧
  ∀ (T T' : NumCore.Simplex 3) (o a b c o' a' b' c' : Fin 4),
    T.Nondeg →
      T'.Nondeg →
        [o, a, b, c].Nodup →
          [o', a', b', c'].Nodup →
            T'.x a' = T.x a →
              T'.x b' = T.x b →
                T'.x c' = T.x c →
                  let nv := Paper1.Spec.cross3 (T.x b - T.x a) (T.x c - T.x a);
                  NumCore.dot nv (T.x o - T.x a) * NumCore.dot nv (T'.x o' - T.x a) < 0 → T'.facet o' = -T.facet o
```

CFD `CFDLean.Num.Simplex.facet_cross3` (module `CFDLean.Num.Simplex`):

```lean
(∀ (T : CFDLean.Num.Simplex 3) (o a b c : Fin 4),
    T.Nondeg →
      [o, a, b, c].Nodup →
        let nv := CFDLean.Num.cross3 (T.x b - T.x a) (T.x c - T.x a);
        T.facet o = (if 0 < CFDLean.Num.dot nv (T.x o - T.x a) then -(1 / 2) else 1 / 2) • nv) ∧
  ∀ (T T' : CFDLean.Num.Simplex 3) (o a b c o' a' b' c' : Fin 4),
    T.Nondeg →
      T'.Nondeg →
        [o, a, b, c].Nodup →
          [o', a', b', c'].Nodup →
            T'.x a' = T.x a →
              T'.x b' = T.x b →
                T'.x c' = T.x c →
                  let nv := CFDLean.Num.cross3 (T.x b - T.x a) (T.x c - T.x a);
                  CFDLean.Num.dot nv (T.x o - T.x a) * CFDLean.Num.dot nv (T'.x o' - T.x a) < 0 →
                    T'.facet o' = -T.facet o
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-11.2b: `CFDLean.Num.Simplex.facet_perp2`

JST `Paper1.Spec.P3_11_2b` (proof `Paper1.Proofs.p3_11_2b`):

```lean
∀ (T : NumCore.Simplex 2) (o a b : Fin 3),
  T.Nondeg →
    [o, a, b].Nodup →
      T.facet o =
        (if 0 < NumCore.dot (Paper1.Spec.perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1) •
          Paper1.Spec.perp2 (T.x b - T.x a)
```

CFD `CFDLean.Num.Simplex.facet_perp2` (module `CFDLean.Num.Simplex`):

```lean
∀ (T : CFDLean.Num.Simplex 2) (o a b : Fin 3),
  T.Nondeg →
    [o, a, b].Nodup →
      T.facet o =
        (if 0 < CFDLean.Num.dot (CFDLean.Num.perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1) •
          CFDLean.Num.perp2 (T.x b - T.x a)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-12.5: `CFDLean.Num.pathSimplex_nonobtuse`

JST `Paper1.Spec.P3_12_5` (proof `Paper1.Proofs.p3_12_5`):

```lean
∀ (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ),
  (∀ (i : Fin 3), 0 < h i) →
    (Paper1.Spec.pathSimplex π h).Nondeg ∧
      ∀ (a b : Fin 4),
        a ≠ b → NumCore.dot ((Paper1.Spec.pathSimplex π h).grad a) ((Paper1.Spec.pathSimplex π h).grad b) ≤ 0
```

CFD `CFDLean.Num.pathSimplex_nonobtuse` (module `CFDLean.Num.Simplex`):

```lean
∀ (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ),
  (∀ (i : Fin 3), 0 < h i) →
    (CFDLean.Num.pathSimplex π h).Nondeg ∧
      ∀ (a b : Fin 4),
        a ≠ b → CFDLean.Num.dot ((CFDLean.Num.pathSimplex π h).grad a) ((CFDLean.Num.pathSimplex π h).grad b) ≤ 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-2.3: `CFDLean.Num.WMesh.nW_row_sum`

JST `Paper1.Spec.P1_2_3` (proof `Paper1.Proofs.p1_2_3`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (W : C → Fin (d + 1) → ℝ),
  M.Valid →
    (∀ (T : C), ∑ a, W T a = M.vol T) → (∀ (i : ι), ∑ k, M.nW W i k = -M.beta i) ∧ ∀ (i : ι), M.Closed i → M.beta i = 0
```

CFD `CFDLean.Num.WMesh.nW_row_sum` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (W : C → Fin (d + 1) → ℝ),
  M.Valid →
    (∀ (T : C), ∑ a, W T a = M.vol T) → (∀ (i : ι), ∑ k, M.nW W i k = -M.beta i) ∧ ∀ (i : ι), M.Closed i → M.beta i = 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.1: `CFDLean.Num.WMesh.sbp_defect`

JST `Paper1.Spec.P2_6_1` (proof `Paper1.Proofs.p2_6_1`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (W : C → Fin (d + 1) → ℝ),
  (∀ (T : C), ∑ a, W T a = M.vol T) →
    (∀ (i k : ι), M.cW W i k + M.cW W k i = M.B i k + 2 • M.EW W i k) ∧
      (∀ (i k : ι), M.EW W k i = M.EW W i k) ∧
        (∀ (i : ι), ∑ k, M.EW W i k = 0) ∧ (∀ (i : ι), ∑ k, M.cW W i k = 0) ∧ ∀ (k : ι), ∑ i, M.cW W i k = M.beta k
```

CFD `CFDLean.Num.WMesh.sbp_defect` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (W : C → Fin (d + 1) → ℝ),
  (∀ (T : C), ∑ a, W T a = M.vol T) →
    (∀ (i k : ι), M.cW W i k + M.cW W k i = M.B i k + 2 • M.EW W i k) ∧
      (∀ (i k : ι), M.EW W k i = M.EW W i k) ∧
        (∀ (i : ι), ∑ k, M.EW W i k = 0) ∧ (∀ (i : ι), ∑ k, M.cW W i k = 0) ∧ ∀ (k : ι), ∑ i, M.cW W i k = M.beta k
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.2: `CFDLean.Num.Simplex.median_defect_iff`

JST `Paper1.Spec.P2_6_2` (proof `Paper1.Proofs.p2_6_2`):

```lean
∀ (d : ℕ) (T : NumCore.Simplex d) (δ : Fin (d + 1) → ℝ),
  1 ≤ d →
    T.Nondeg →
      ∑ a, δ a = 0 →
        ((∀ (a b : Fin (d + 1)), a ≠ b → δ a • T.grad b + δ b • T.grad a = 0) ↔ ∀ (a : Fin (d + 1)), δ a = 0)
```

CFD `CFDLean.Num.Simplex.median_defect_iff` (module `CFDLean.Num.Mesh`):

```lean
∀ (d : ℕ) (T : CFDLean.Num.Simplex d) (δ : Fin (d + 1) → ℝ),
  1 ≤ d →
    T.Nondeg →
      ∑ a, δ a = 0 →
        ((∀ (a b : Fin (d + 1)), a ≠ b → δ a • T.grad b + δ b • T.grad a = 0) ↔ ∀ (a : Fin (d + 1)), δ a = 0)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.2: `CFDLean.Num.WMesh.dissGeom_edge`

JST `Paper1.Spec.P1_5_2` (proof `Paper1.Proofs.p1_5_2`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d),
  M.Valid →
    (∀ (i k : ι), i ≠ k → NumCore.dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧
      ∀ (i k : ι),
        i ≠ k →
          (∃ T a b, (M.vert T) a = i ∧ (M.vert T) b = k ∧ 0 < M.ω T) →
            0 < M.mu i k ∧
              (∃ t, 0 < t ∧ M.nu i k = t • M.e i k) ∧
                NumCore.len (M.nu i k) = NumCore.dot (M.n i k) (M.e i k) / NumCore.len (M.e i k)
```

CFD `CFDLean.Num.WMesh.dissGeom_edge` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ)
  (M : CFDLean.Num.WMesh ι C d),
  M.Valid →
    (∀ (i k : ι), i ≠ k → CFDLean.Num.dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧
      ∀ (i k : ι),
        i ≠ k →
          (∃ T a b, (M.vert T) a = i ∧ (M.vert T) b = k ∧ 0 < M.ω T) →
            0 < M.mu i k ∧
              (∃ t, 0 < t ∧ M.nu i k = t • M.e i k) ∧
                CFDLean.Num.len (M.nu i k) = CFDLean.Num.dot (M.n i k) (M.e i k) / CFDLean.Num.len (M.e i k)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.3: `CFDLean.Num.WMesh.dissGeom_outer`

JST `Paper1.Spec.P1_5_3` (proof `Paper1.Proofs.p1_5_3`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d),
  M.Valid →
    (∀ (i : ι), ∑ k, NumCore.outer (M.c i k) (M.e i k) = M.V i • 1) ∧
      (∀ (i : ι), M.Closed i → ∑ k, NumCore.outer (M.n i k) (M.e i k) = (2 * M.V i) • 1) ∧
        ∑ i, ∑ k, NumCore.outer (M.n i k) (M.e i k) = (2 * M.volΩ) • 1 ∧ ∑ i, M.V i = M.volΩ
```

CFD `CFDLean.Num.WMesh.dissGeom_outer` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d),
  M.Valid →
    (∀ (i : ι), ∑ k, CFDLean.Num.outer (M.c i k) (M.e i k) = M.V i • 1) ∧
      (∀ (i : ι), M.Closed i → ∑ k, CFDLean.Num.outer (M.n i k) (M.e i k) = (2 * M.V i) • 1) ∧
        ∑ i, ∑ k, CFDLean.Num.outer (M.n i k) (M.e i k) = (2 * M.volΩ) • 1 ∧ ∑ i, M.V i = M.volΩ
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.4: `CFDLean.Num.WMesh.dissGeom_calibration`

JST `Paper1.Spec.P1_5_4` (proof `Paper1.Proofs.p1_5_4`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d),
  M.Valid →
    (∀ (i : ι), M.Closed i → (M.Gtensor M.nu i).trace = 2 * ↑d * M.V i) ∧
      ∑ i, ∑ k, NumCore.len (M.nu i k) * NumCore.len (M.e i k) = 2 * ↑d * M.volΩ ∧
        (∀ (i : ι), M.Closed i → 2 * ↑d * M.V i ≤ (M.Gtensor M.n i).trace) ∧
          ∀ (i : ι),
            M.Closed i → ((M.Gtensor M.n i).trace = 2 * ↑d * M.V i ↔ ∀ (k : ι), ∃ t, 0 ≤ t ∧ M.n i k = t • M.e i k)
```

CFD `CFDLean.Num.WMesh.dissGeom_calibration` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] (d : ℕ) (M : CFDLean.Num.WMesh ι C d),
  M.Valid →
    (∀ (i : ι), M.Closed i → (M.Gtensor M.nu i).trace = 2 * ↑d * M.V i) ∧
      ∑ i, ∑ k, CFDLean.Num.len (M.nu i k) * CFDLean.Num.len (M.e i k) = 2 * ↑d * M.volΩ ∧
        (∀ (i : ι), M.Closed i → 2 * ↑d * M.V i ≤ (M.Gtensor M.n i).trace) ∧
          ∀ (i : ι),
            M.Closed i → ((M.Gtensor M.n i).trace = 2 * ↑d * M.V i ↔ ∀ (k : ι), ∃ t, 0 ≤ t ∧ M.n i k = t • M.e i k)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-7.1: `CFDLean.Num.quadratic_edge_expansion`

JST `Paper1.Spec.P2_7_1` (proof `Paper1.Proofs.p2_7_1`):

```lean
∀ (ι : Type) [inst : Fintype ι] (d : ℕ) (x : ι → NumCore.Vec d) (i : ι) (lam : ι → ℝ)
  (V q0 : ℝ) (gq : NumCore.Vec d) (H : Matrix (Fin d) (Fin d) ℝ),
  V ≠ 0 →
    H.IsSymm →
      let q := fun z => q0 + NumCore.dot gq z + 1 / 2 * NumCore.dot z (H.mulVec z);
      let K := (1 / (4 * V)) • ∑ k, lam k • NumCore.outer (x k - x i) (x k - x i);
      1 / 2 * ∑ k, lam k * (q (x k) - q (x i)) =
        1 / 2 * ∑ k, lam k * NumCore.dot (gq + H.mulVec (x i)) (x k - x i) + V * NumCore.frob K H
```

CFD `CFDLean.Num.quadratic_edge_expansion` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι : Type) [inst : Fintype ι] (d : ℕ) (x : ι → CFDLean.Num.Vec d) (i : ι)
  (lam : ι → ℝ) (V q0 : ℝ) (gq : CFDLean.Num.Vec d) (H : Matrix (Fin d) (Fin d) ℝ),
  V ≠ 0 →
    H.IsSymm →
      let q := fun z => q0 + CFDLean.Num.dot gq z + 1 / 2 * CFDLean.Num.dot z (H.mulVec z);
      let K := (1 / (4 * V)) • ∑ k, lam k • CFDLean.Num.outer (x k - x i) (x k - x i);
      1 / 2 * ∑ k, lam k * (q (x k) - q (x i)) =
        1 / 2 * ∑ k, lam k * CFDLean.Num.dot (gq + H.mulVec (x i)) (x k - x i) + V * CFDLean.Num.frob K H
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-7.2: `CFDLean.Num.dissTensor_loewner`

JST `Paper1.Spec.P2_7_2` (proof `Paper1.Proofs.p2_7_2`):

```lean
∀ (ι : Type) [inst : Fintype ι] (d : ℕ) (e y : ι → NumCore.Vec d) (σ : ι → ℝ) (V : ℝ),
  0 < V →
    (∀ (k : ι), 0 ≤ σ k) →
      (∀ (k : ι), 0 < NumCore.dot (y k) (e k)) →
        let K := fun z => (1 / (4 * V)) • ∑ k, (σ k * NumCore.len (z k)) • NumCore.outer (e k) (e k);
        let ν := fun k => NumCore.WMesh.nuOf (y k) (e k);
        (∀ (k : ι),
            NumCore.len (y k) = NumCore.len (ν k) * (NumCore.len (y k) * NumCore.len (e k) / NumCore.dot (y k) (e k)) ∧
              1 ≤ NumCore.len (y k) * NumCore.len (e k) / NumCore.dot (y k) (e k)) ∧
          (K y - K ν).PosSemidef ∧ (K y = K ν ↔ ∀ (k : ι), 0 < σ k → ∃ t, 0 < t ∧ y k = t • e k)
```

CFD `CFDLean.Num.dissTensor_loewner` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι : Type) [inst : Fintype ι] (d : ℕ) (e y : ι → CFDLean.Num.Vec d) (σ : ι → ℝ)
  (V : ℝ),
  0 < V →
    (∀ (k : ι), 0 ≤ σ k) →
      (∀ (k : ι), 0 < CFDLean.Num.dot (y k) (e k)) →
        let K := fun z => (1 / (4 * V)) • ∑ k, (σ k * CFDLean.Num.len (z k)) • CFDLean.Num.outer (e k) (e k);
        let ν := fun k => CFDLean.Num.WMesh.nuOf (y k) (e k);
        (∀ (k : ι),
            CFDLean.Num.len (y k) =
                CFDLean.Num.len (ν k) * (CFDLean.Num.len (y k) * CFDLean.Num.len (e k) / CFDLean.Num.dot (y k) (e k)) ∧
              1 ≤ CFDLean.Num.len (y k) * CFDLean.Num.len (e k) / CFDLean.Num.dot (y k) (e k)) ∧
          (K y - K ν).PosSemidef ∧ (K y = K ν ↔ ∀ (k : ι), 0 < σ k → ∃ t, 0 < t ∧ y k = t • e k)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-7.3: `CFDLean.Num.WMesh.dissTensor_trace`

JST `Paper1.Spec.P2_7_3` (proof `Paper1.Proofs.p2_7_3`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (σ : ι → ι → ℝ) (s σmax h : ℝ) (y : ι → ι → NumCore.Vec d) (i : ι),
  M.Valid →
    0 < M.V i →
      let K := fun z => (1 / (4 * M.V i)) • ∑ k, (σ i k * NumCore.len (z i k)) • NumCore.outer (M.e i k) (M.e i k);
      ((∀ (k : ι), k ≠ i → σ i k * NumCore.len (M.e i k) = s) → K y = (s / (4 * M.V i)) • M.Gtensor y i) ∧
        ((∀ (k : ι), k ≠ i → σ i k * NumCore.len (M.e i k) = s) → (K M.nu).trace = ↑d * s / 2) ∧
          ((∀ (k : ι), 0 ≤ σ i k ∧ σ i k ≤ σmax) →
            (∀ (k : ι), M.n i k ≠ 0 → NumCore.len (M.e i k) ≤ h) → (K M.nu).trace ≤ ↑d / 2 * σmax * h)
```

CFD `CFDLean.Num.WMesh.dissTensor_trace` (module `CFDLean.Num.Mesh`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (σ : ι → ι → ℝ) (s σmax h : ℝ)
  (y : ι → ι → CFDLean.Num.Vec d) (i : ι),
  M.Valid →
    0 < M.V i →
      let K := fun z =>
        (1 / (4 * M.V i)) • ∑ k, (σ i k * CFDLean.Num.len (z i k)) • CFDLean.Num.outer (M.e i k) (M.e i k);
      ((∀ (k : ι), k ≠ i → σ i k * CFDLean.Num.len (M.e i k) = s) → K y = (s / (4 * M.V i)) • M.Gtensor y i) ∧
        ((∀ (k : ι), k ≠ i → σ i k * CFDLean.Num.len (M.e i k) = s) → (K M.nu).trace = ↑d * s / 2) ∧
          ((∀ (k : ι), 0 ≤ σ i k ∧ σ i k ≤ σmax) →
            (∀ (k : ι), M.n i k ≠ 0 → CFDLean.Num.len (M.e i k) ≤ h) → (K M.nu).trace ≤ ↑d / 2 * σmax * h)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.0a: `CFDLean.Num.WMesh.closed_of_facetPaired`

JST `Paper1.Spec.P1_5_0a` (proof `Paper1.Proofs.p1_5_0a`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (i : ι), M.Valid → M.FacetPaired i → M.Closed i
```

CFD `CFDLean.Num.WMesh.closed_of_facetPaired` (module `CFDLean.Num.Boundary`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (i : ι), M.Valid → M.FacetPaired i → M.Closed i
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.3: `CFDLean.Num.WMesh.conforming_boundary`

JST `Paper1.Spec.P2_6_3` (proof `Paper1.Proofs.p2_6_3`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧
          (∀ (i k : ι),
              M.B i k =
                ∑ p,
                  if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
                    ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p
                  else 0) ∧
            ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i
```

CFD `CFDLean.Num.WMesh.conforming_boundary` (module `CFDLean.Num.Boundary`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (bd : C × Fin (d + 1) → Bool),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧
          (∀ (i k : ι),
              M.B i k =
                ∑ p,
                  if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
                    ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p
                  else 0) ∧
            ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-11.1: `CFDLean.Num.WMesh.facetBalanced_boundary`

JST `Paper1.Spec.P3_11_1` (proof `Paper1.Proofs.p3_11_1`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ)
  (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool),
  M.Valid →
    1 ≤ d →
      (M.Conforming bd → M.FacetBalanced bd) ∧
        (M.FacetBalanced bd →
          (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧
            (∀ (i k : ι),
                M.B i k =
                  ∑ p,
                    if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
                      ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p
                    else 0) ∧
              ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i)
```

CFD `CFDLean.Num.WMesh.facetBalanced_boundary` (module `CFDLean.Num.Boundary`):

```lean
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (bd : C × Fin (d + 1) → Bool),
  M.Valid →
    1 ≤ d →
      (M.Conforming bd → M.FacetBalanced bd) ∧
        (M.FacetBalanced bd →
          (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧
            (∀ (i k : ι),
                M.B i k =
                  ∑ p,
                    if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
                      ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p
                    else 0) ∧
              ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-11.4: `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced`

JST `Paper1.Spec.P3_11_4` (proof `Paper1.Proofs.p3_11_4`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : LinearOrder ι]
  [inst_3 : Fintype C] (M : NumCore.WMesh ι C 3) (bd : C × Fin 4 → Bool),
  M.Valid → Paper1.Spec.SideBalanced M bd → M.FacetBalanced bd
```

CFD `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced` (module `CFDLean.Num.Boundary`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : LinearOrder ι] [inst_3 : Fintype C] (M : CFDLean.Num.WMesh ι C 3) (bd : C × Fin 4 → Bool),
  M.Valid → CFDLean.Num.SideBalanced M bd → M.FacetBalanced bd
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-11.4b: `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2`

JST `Paper1.Spec.P3_11_4b` (proof `Paper1.Proofs.p3_11_4b`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : LinearOrder ι]
  [inst_3 : Fintype C] (M : NumCore.WMesh ι C 2) (bd : C × Fin 3 → Bool),
  M.Valid → Paper1.Spec.SideBalanced2 M bd → M.FacetBalanced bd
```

CFD `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2` (module `CFDLean.Num.Boundary`):

```lean
∀ (ι C : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : LinearOrder ι] [inst_3 : Fintype C] (M : CFDLean.Num.WMesh ι C 2) (bd : C × Fin 3 → Bool),
  M.Valid → CFDLean.Num.SideBalanced2 M bd → M.FacetBalanced bd
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-2.1: `CFDLean.Num.antisymmetric_pairFlux`

JST `Paper1.Spec.P1_2_1` (proof `Paper1.Proofs.p1_2_1`):

```lean
∀ (ι κ : Type) [inst : Fintype ι] [inst_1 : Fintype κ] (F : ι → ι → κ → ℝ) (w : ι → κ → ℝ),
  (∀ (i k : ι), F k i = -F i k) →
    ∑ i, ∑ k, F i k = 0 ∧ -∑ i, NumCore.pairF (w i) (∑ k, F i k) = 1 / 2 * ∑ i, ∑ k, NumCore.pairF (w k - w i) (F i k)
```

CFD `CFDLean.Num.antisymmetric_pairFlux` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι κ : Type) [inst : Fintype ι] [inst_1 : Fintype κ] (F : ι → ι → κ → ℝ)
  (w : ι → κ → ℝ),
  (∀ (i k : ι), F k i = -F i k) →
    ∑ i, ∑ k, F i k = 0 ∧
      -∑ i, CFDLean.Num.pairF (w i) (∑ k, F i k) = 1 / 2 * ∑ i, ∑ k, CFDLean.Num.pairF (w k - w i) (F i k)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-2.2: `CFDLean.Num.entropyConservative_production`

JST `Paper1.Spec.P1_2_2` (proof `Paper1.Proofs.p1_2_2`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [inst_1 : Fintype κ] (d : ℕ) (w : S → κ → ℝ)
  (ψ : S → NumCore.Vec d) (Fec : S → S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (u : ι → S),
  (∀ (i k : ι), n k i = -n i k) →
    (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = Fec b a y) →
      (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
        (∀ (a b : S) (y : NumCore.Vec d), NumCore.pairF (w b - w a) (Fec a b y) = NumCore.dot (ψ b - ψ a) y) →
          let beta := fun i => -∑ k, n i k;
          let Rc := fun i => ∑ k, Fec (u i) (u k) (n i k);
          -∑ i, NumCore.pairF (w (u i)) (Rc i) = 1 / 2 * ∑ i, ∑ k, NumCore.dot (ψ (u k) - ψ (u i)) (n i k) ∧
            1 / 2 * ∑ i, ∑ k, NumCore.dot (ψ (u k) - ψ (u i)) (n i k) = ∑ i, NumCore.dot (ψ (u i)) (beta i)
```

CFD `CFDLean.Num.entropyConservative_production` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [inst_1 : Fintype κ] (d : ℕ)
  (w : S → κ → ℝ) (ψ : S → CFDLean.Num.Vec d) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ) (n : ι → ι → CFDLean.Num.Vec d)
  (u : ι → S),
  (∀ (i k : ι), n k i = -n i k) →
    (∀ (a b : S) (y : CFDLean.Num.Vec d), Fec a b y = Fec b a y) →
      (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
        (∀ (a b : S) (y : CFDLean.Num.Vec d),
            CFDLean.Num.pairF (w b - w a) (Fec a b y) = CFDLean.Num.dot (ψ b - ψ a) y) →
          let beta := fun i => -∑ k, n i k;
          let Rc := fun i => ∑ k, Fec (u i) (u k) (n i k);
          -∑ i, CFDLean.Num.pairF (w (u i)) (Rc i) = 1 / 2 * ∑ i, ∑ k, CFDLean.Num.dot (ψ (u k) - ψ (u i)) (n i k) ∧
            1 / 2 * ∑ i, ∑ k, CFDLean.Num.dot (ψ (u k) - ψ (u i)) (n i k) = ∑ i, CFDLean.Num.dot (ψ (u i)) (beta i)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-2.6: `CFDLean.Num.dissipativePairFlux_conservation`

JST `Paper1.Spec.P1_2_6` (proof `Paper1.Proofs.p1_2_6`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ)
  (Fec : S → S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (u : ι → S) (ut : ι → κ → ℝ)
  (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι) (b : ι → κ → ℝ),
  (∀ (i k : ι), n k i = -n i k) →
    (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = Fec b a y) →
      (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
        (∀ (i k : ι), lam k i = lam i k) →
          (∀ (i k : ι), eps2 k i = eps2 i k) →
            (∀ (i k : ι), eps4 k i = eps4 i k) →
              let L := fun i => ∑ k ∈ Nstar i, (ut k - ut i);
              let F := fun i k =>
                Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k));
              (∀ (i k : ι), F k i = -F i k) ∧ ∑ i, (-∑ k, F i k - b i) = -∑ i, b i
```

CFD `CFDLean.Num.dissipativePairFlux_conservation` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ]
  (d : ℕ) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ) (n : ι → ι → CFDLean.Num.Vec d) (u : ι → S) (ut : ι → κ → ℝ)
  (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι) (b : ι → κ → ℝ),
  (∀ (i k : ι), n k i = -n i k) →
    (∀ (a b : S) (y : CFDLean.Num.Vec d), Fec a b y = Fec b a y) →
      (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
        (∀ (i k : ι), lam k i = lam i k) →
          (∀ (i k : ι), eps2 k i = eps2 i k) →
            (∀ (i k : ι), eps4 k i = eps4 i k) →
              let L := fun i => ∑ k ∈ Nstar i, (ut k - ut i);
              let F := fun i k =>
                Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k));
              (∀ (i k : ι), F k i = -F i k) ∧ ∑ i, (-∑ k, F i k - b i) = -∑ i, b i
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-2.7: `CFDLean.Num.dissipativePairFlux_freeStream`

JST `Paper1.Spec.P1_2_7` (proof `Paper1.Proofs.p1_2_7`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ)
  (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (U : S)
  (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι),
  (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
    (∀ (y : NumCore.Vec d), Fec U U y = phys U y) →
      let beta := fun i => -∑ k, n i k;
      let L := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0);
      let F := fun i k => Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k));
      ∀ (i : ι), -∑ k, F i k - phys U (beta i) = 0
```

CFD `CFDLean.Num.dissipativePairFlux_freeStream` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ]
  (d : ℕ) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ) (phys : S → CFDLean.Num.Vec d → κ → ℝ)
  (n : ι → ι → CFDLean.Num.Vec d) (U : S) (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι),
  (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
    (∀ (y : CFDLean.Num.Vec d), Fec U U y = phys U y) →
      let beta := fun i => -∑ k, n i k;
      let L := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0);
      let F := fun i k => Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k));
      ∀ (i : ι), -∑ k, F i k - phys U (beta i) = 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.4: `CFDLean.Num.edgeForm_boundary_split`

JST `Paper1.Spec.P2_6_4` (proof `Paper1.Proofs.p2_6_4`):

```lean
∀ (ι κ : Type) [inst : Fintype ι] [Fintype κ] (d : ℕ) (c B : ι → ι → NumCore.Vec d)
  (β : ι → NumCore.Vec d) (F : ι → Matrix κ (Fin d) ℝ),
  (∀ (i : ι), ∑ k, c i k = 0) →
    (∀ (k : ι), ∑ i, c i k = β k) →
      (∀ (i : ι), ∑ k, B i k = β i) →
        let n := fun i k => c i k - c k i;
        let s := fun i k => (1 / 2) • (c i k + c k i - B i k);
        ∀ (i : ι),
          ∑ k, ((1 / 2) • (F i + F k)).mulVec (n i k) + ∑ k, (F k - F i).mulVec (s i k) +
              (1 / 2) • (∑ k, (F k).mulVec (B i k) + (F i).mulVec (β i)) =
            ∑ k, (F k).mulVec (c i k)
```

CFD `CFDLean.Num.edgeForm_boundary_split` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι κ : Type) [inst : Fintype ι] [Fintype κ] (d : ℕ)
  (c B : ι → ι → CFDLean.Num.Vec d) (β : ι → CFDLean.Num.Vec d) (F : ι → Matrix κ (Fin d) ℝ),
  (∀ (i : ι), ∑ k, c i k = 0) →
    (∀ (k : ι), ∑ i, c i k = β k) →
      (∀ (i : ι), ∑ k, B i k = β i) →
        let n := fun i k => c i k - c k i;
        let s := fun i k => (1 / 2) • (c i k + c k i - B i k);
        ∀ (i : ι),
          ∑ k, ((1 / 2) • (F i + F k)).mulVec (n i k) + ∑ k, (F k - F i).mulVec (s i k) +
              (1 / 2) • (∑ k, (F k).mulVec (B i k) + (F i).mulVec (β i)) =
            ∑ k, (F k).mulVec (c i k)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.5: `CFDLean.Num.WMesh.standardClosure_entropy`

JST `Paper1.Spec.P2_6_5` (proof `Paper1.Proofs.p2_6_5`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  [inst_3 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (w : ι → κ → ℝ)
  (ψ : ι → NumCore.Vec d) (Fs : C × Fin (d + 1) → ι → κ → ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        let b := fun i =>
          ∑ p,
            if bd p = Bool.true ∧ i ∈ M.facetNodes p then ∑ j ∈ M.facetNodes p, Paper1.Spec.stdWeight d i j • Fs p j
            else 0;
        ∑ i, (NumCore.dot (ψ i) (M.beta i) - NumCore.pairF (w i) (b i)) =
          ∑ p,
            if bd p = Bool.true then
              1 / ↑d * ∑ i ∈ M.facetNodes p, (NumCore.dot (ψ i) (M.areaVec p) - NumCore.pairF (w i) (Fs p i)) +
                1 / (4 * ↑d * (↑d + 1)) *
                  ∑ i ∈ M.facetNodes p, ∑ j ∈ M.facetNodes p, NumCore.pairF (w j - w i) (Fs p j - Fs p i)
            else 0
```

CFD `CFDLean.Num.WMesh.standardClosure_entropy` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] [inst_3 : Fintype κ] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (bd : C × Fin (d + 1) → Bool)
  (w : ι → κ → ℝ) (ψ : ι → CFDLean.Num.Vec d) (Fs : C × Fin (d + 1) → ι → κ → ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        let b := fun i =>
          ∑ p,
            if bd p = Bool.true ∧ i ∈ M.facetNodes p then ∑ j ∈ M.facetNodes p, CFDLean.Num.stdWeight d i j • Fs p j
            else 0;
        ∑ i, (CFDLean.Num.dot (ψ i) (M.beta i) - CFDLean.Num.pairF (w i) (b i)) =
          ∑ p,
            if bd p = Bool.true then
              1 / ↑d * ∑ i ∈ M.facetNodes p, (CFDLean.Num.dot (ψ i) (M.areaVec p) - CFDLean.Num.pairF (w i) (Fs p i)) +
                1 / (4 * ↑d * (↑d + 1)) *
                  ∑ i ∈ M.facetNodes p, ∑ j ∈ M.facetNodes p, CFDLean.Num.pairF (w j - w i) (Fs p j - Fs p i)
            else 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.5b: `CFDLean.Num.WMesh.standardClosure_linear`

JST `Paper1.Spec.P2_6_5b` (proof `Paper1.Proofs.p2_6_5b`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  [Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (F : ι → Matrix κ (Fin d) ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (i : ι),
            ∑ k, (F k).mulVec ((1 / 2) • (M.B i k + if i = k then M.beta i else 0)) =
              ∑ p,
                if bd p = Bool.true ∧ i ∈ M.facetNodes p then
                  ∑ j ∈ M.facetNodes p, Paper1.Spec.stdWeight d i j • (F j).mulVec (M.areaVec p)
                else 0) ∧
          ∀ (i j : ι), i ≠ j → Paper1.Spec.stdWeight d i i = (↑d + 3) * Paper1.Spec.stdWeight d i j
```

CFD `CFDLean.Num.WMesh.standardClosure_linear` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] [Fintype κ] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (bd : C × Fin (d + 1) → Bool)
  (F : ι → Matrix κ (Fin d) ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (i : ι),
            ∑ k, (F k).mulVec ((1 / 2) • (M.B i k + if i = k then M.beta i else 0)) =
              ∑ p,
                if bd p = Bool.true ∧ i ∈ M.facetNodes p then
                  ∑ j ∈ M.facetNodes p, CFDLean.Num.stdWeight d i j • (F j).mulVec (M.areaVec p)
                else 0) ∧
          ∀ (i j : ι), i ≠ j → CFDLean.Num.stdWeight d i i = (↑d + 3) * CFDLean.Num.stdWeight d i j
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-8.1: `CFDLean.Num.quadratureClosure_entropy`

JST `Paper1.Spec.P2_8_1` (proof `Paper1.Proofs.p2_8_1`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [inst_2 : Fintype κ] (d : ℕ)
  (w : S → κ → ℝ) (ψ : S → NumCore.Vec d) (Fec : S → S → NumCore.Vec d → κ → ℝ) (u : ι → S) (φ : Q → ι → ℝ)
  (N : Q → NumCore.Vec d) (ut : Q → S) (Fs : Q → κ → ℝ),
  (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = Fec b a y) →
    (∀ (a b : S) (y : NumCore.Vec d), NumCore.pairF (w b - w a) (Fec a b y) = NumCore.dot (ψ b - ψ a) y) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        (∀ (q : Q), w (ut q) = ∑ k, φ q k • w (u k)) →
          let beta := fun i => ∑ q, φ q i • N q;
          let b := fun i => ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q);
          ∑ i, (NumCore.dot (ψ (u i)) (beta i) - NumCore.pairF (w (u i)) (b i)) =
              ∑ q, (NumCore.dot (ψ (ut q)) (N q) - NumCore.pairF (w (ut q)) (Fs q)) ∧
            ∑ i, b i = ∑ q, Fs q
```

CFD `CFDLean.Num.quadratureClosure_entropy` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q]
  [inst_2 : Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → CFDLean.Num.Vec d) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ)
  (u : ι → S) (φ : Q → ι → ℝ) (N : Q → CFDLean.Num.Vec d) (ut : Q → S) (Fs : Q → κ → ℝ),
  (∀ (a b : S) (y : CFDLean.Num.Vec d), Fec a b y = Fec b a y) →
    (∀ (a b : S) (y : CFDLean.Num.Vec d), CFDLean.Num.pairF (w b - w a) (Fec a b y) = CFDLean.Num.dot (ψ b - ψ a) y) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        (∀ (q : Q), w (ut q) = ∑ k, φ q k • w (u k)) →
          let beta := fun i => ∑ q, φ q i • N q;
          let b := fun i => ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + Fs q);
          ∑ i, (CFDLean.Num.dot (ψ (u i)) (beta i) - CFDLean.Num.pairF (w (u i)) (b i)) =
              ∑ q, (CFDLean.Num.dot (ψ (ut q)) (N q) - CFDLean.Num.pairF (w (ut q)) (Fs q)) ∧
            ∑ i, b i = ∑ q, Fs q
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-8.2: `CFDLean.Num.quadratureClosure_freeStream`

JST `Paper1.Spec.P2_8_2` (proof `Paper1.Proofs.p2_8_2`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ] (d : ℕ)
  (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ)
  (N : Q → NumCore.Vec d) (n : ι → ι → NumCore.Vec d),
  (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
    (∀ (y : NumCore.Vec d), Fec U U y = phys U y) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        (∀ (i : ι), ∑ q, φ q i • N q = -∑ k, n i k) →
          let b := fun i => ∑ q, φ q i • (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q));
          ∀ (i : ι), -∑ k, Fec U U (n i k) - b i = 0
```

CFD `CFDLean.Num.quadratureClosure_freeStream` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ]
  (d : ℕ) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ) (phys : S → CFDLean.Num.Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ)
  (N : Q → CFDLean.Num.Vec d) (n : ι → ι → CFDLean.Num.Vec d),
  (∀ (a b : S), IsLinearMap ℝ (Fec a b)) →
    (∀ (y : CFDLean.Num.Vec d), Fec U U y = phys U y) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        (∀ (i : ι), ∑ q, φ q i • N q = -∑ k, n i k) →
          let b := fun i => ∑ q, φ q i • (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q));
          ∀ (i : ι), -∑ k, Fec U U (n i k) - b i = 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-8.3: `CFDLean.Num.quadratureClosure_linear`

JST `Paper1.Spec.P2_8_3` (proof `Paper1.Proofs.p2_8_3`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ] (d : ℕ)
  (Fec : S → S → NumCore.Vec d → κ → ℝ) (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ)
  (N : Q → NumCore.Vec d) (ut : Q → S),
  (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = ((1 / 2) • (Fl a + Fl b)).mulVec y) →
    (∀ (q : Q), Fl (ut q) = ∑ k, φ q k • Fl (u k)) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        let beta := fun i => ∑ q, φ q i • N q;
        let b := fun i =>
          ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q));
        ∀ (i : ι), b i = (1 / 2) • ((Fl (u i)).mulVec (beta i) + ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q))
```

CFD `CFDLean.Num.quadratureClosure_linear` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ]
  (d : ℕ) (Fec : S → S → CFDLean.Num.Vec d → κ → ℝ) (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ)
  (N : Q → CFDLean.Num.Vec d) (ut : Q → S),
  (∀ (a b : S) (y : CFDLean.Num.Vec d), Fec a b y = ((1 / 2) • (Fl a + Fl b)).mulVec y) →
    (∀ (q : Q), Fl (ut q) = ∑ k, φ q k • Fl (u k)) →
      (∀ (q : Q), ∑ k, φ q k = 1) →
        let beta := fun i => ∑ q, φ q i • N q;
        let b := fun i =>
          ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q));
        ∀ (i : ι), b i = (1 / 2) • ((Fl (u i)).mulVec (beta i) + ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q))
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-8.4: `CFDLean.Num.WMesh.faceRule_beta_B`

JST `Paper1.Spec.P2_8_4` (proof `Paper1.Proofs.p2_8_4`):

```lean
∀ (ι C Q : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  [inst_2 : DecidableEq C] [inst_3 : Fintype Q] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool)
  (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (q : Q), bd (fq q) = Bool.true) →
          (∀ (q : Q), ∀ k ∉ M.facetNodes (fq q), φ q k = 0) →
            (∀ (p : C × Fin (d + 1)),
                bd p = Bool.true → ∀ i ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / ↑d) →
              (∀ (p : C × Fin (d + 1)),
                  bd p = Bool.true →
                    ∀ i ∈ M.facetNodes p,
                      ∀ k ∈ M.facetNodes p,
                        (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) =
                          (1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) →
                let N := fun q => aq q • M.areaVec (fq q);
                (∀ (i : ι), ∑ q, φ q i • N q = M.beta i) ∧ ∀ (i k : ι), ∑ q, (φ q i * φ q k) • N q = M.B i k
```

CFD `CFDLean.Num.WMesh.faceRule_beta_B` (module `CFDLean.Num.PairFlux`):

```lean
∀ (ι C Q : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  [inst_2 : DecidableEq C] [inst_3 : Fintype Q] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (bd : C × Fin (d + 1) → Bool)
  (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ),
  M.Valid →
    1 ≤ d →
      M.Conforming bd →
        (∀ (q : Q), bd (fq q) = Bool.true) →
          (∀ (q : Q), ∀ k ∉ M.facetNodes (fq q), φ q k = 0) →
            (∀ (p : C × Fin (d + 1)),
                bd p = Bool.true → ∀ i ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / ↑d) →
              (∀ (p : C × Fin (d + 1)),
                  bd p = Bool.true →
                    ∀ i ∈ M.facetNodes p,
                      ∀ k ∈ M.facetNodes p,
                        (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) =
                          (1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) →
                let N := fun q => aq q • M.areaVec (fq q);
                (∀ (i : ι), ∑ q, φ q i • N q = M.beta i) ∧ ∀ (i k : ι), ∑ q, (φ q i * φ q k) • N q = M.B i k
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-4.1: `CFDLean.Num.WMesh.galerkin_identity`

JST `Paper1.Spec.P1_4_1` (proof `Paper1.Proofs.p1_4_1`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C]
  [inst_3 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (w : ι → κ → ℝ) (Fl : C → Matrix κ (Fin d) ℝ),
  ∑ i, NumCore.pairF (w i) (M.galerkinRes Fl i) = -∑ T, M.ω T * M.vol T * NumCore.frob (M.gradW w T) (Fl T)
```

CFD `CFDLean.Num.WMesh.galerkin_identity` (module `CFDLean.Num.Galerkin`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] [inst_3 : Fintype κ] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (w : ι → κ → ℝ)
  (Fl : C → Matrix κ (Fin d) ℝ),
  ∑ i, CFDLean.Num.pairF (w i) (M.galerkinRes Fl i) = -∑ T, M.ω T * M.vol T * CFDLean.Num.frob (M.gradW w T) (Fl T)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.5: `CFDLean.Num.WMesh.fvRes_eq_galerkinRes`

JST `Paper1.Spec.P1_5_5` (proof `Paper1.Proofs.p1_5_5`):

```lean
∀ (ι C κ : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : Fintype κ]
  (d : ℕ) (M : NumCore.WMesh ι C d) (S : C → ι → ι → NumCore.Vec d) (Fl : C → Matrix κ (Fin d) ℝ),
  (∀ (T : C) (a b : Fin (d + 1)), S T ((M.vert T) a) ((M.vert T) b) = M.m T • (M.g T b - M.g T a)) →
    ∀ (i : ι), M.fvRes Fl S i = M.galerkinRes Fl i
```

CFD `CFDLean.Num.WMesh.fvRes_eq_galerkinRes` (module `CFDLean.Num.Galerkin`):

```lean
∀ (ι C κ : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C]
  [inst_2 : Fintype κ] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (S : C → ι → ι → CFDLean.Num.Vec d)
  (Fl : C → Matrix κ (Fin d) ℝ),
  (∀ (T : C) (a b : Fin (d + 1)), S T ((M.vert T) a) ((M.vert T) b) = M.m T • (M.g T b - M.g T a)) →
    ∀ (i : ι), M.fvRes Fl S i = M.galerkinRes Fl i
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P2-6.7: `CFDLean.Num.WMesh.closed_mean_galerkin`

JST `Paper1.Spec.P2_6_7` (proof `Paper1.Proofs.p2_6_7`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] [Fintype κ]
  (d : ℕ) (M : NumCore.WMesh ι C d) (F : ι → Matrix κ (Fin d) ℝ) (i : ι),
  M.Valid →
    M.Closed i →
      ∑ k, ((1 / 2) • (F i + F k)).mulVec (M.n i k) = ∑ k, (F k).mulVec (M.c i k) ∧
        ∑ k, (F k).mulVec (M.c i k) =
          ∑ T, ∑ a, if (M.vert T) a = i then (M.ω T * M.m T) • ∑ b, (F ((M.vert T) b)).mulVec (M.g T b) else 0
```

CFD `CFDLean.Num.WMesh.closed_mean_galerkin` (module `CFDLean.Num.Galerkin`):

```lean
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι]
  [inst_2 : Fintype C] [Fintype κ] (d : ℕ) (M : CFDLean.Num.WMesh ι C d) (F : ι → Matrix κ (Fin d) ℝ) (i : ι),
  M.Valid →
    M.Closed i →
      ∑ k, ((1 / 2) • (F i + F k)).mulVec (M.n i k) = ∑ k, (F k).mulVec (M.c i k) ∧
        ∑ k, (F k).mulVec (M.c i k) =
          ∑ T, ∑ a, if (M.vert T) a = i then (M.ω T * M.m T) • ∑ b, (F ((M.vert T) b)).mulVec (M.g T b) else 0
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P3-13.1: `CFDLean.Num.pair_production_integral`

JST `Paper1.Spec.P3_13_1` (proof `Paper1.Proofs.p3_13_1`):

```lean
∀ (κ : Type) [inst : Fintype κ] (Φ : (κ → ℝ) → κ → ℝ) (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] κ → ℝ)
  (wi wk : κ → ℝ),
  (∀ s ∈ Set.Icc 0 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) →
    ContinuousOn (fun s => (B (wi + s • (wk - wi))) (wk - wi)) (Set.Icc 0 1) →
      Φ wk - Φ wi = ∫ (s : ℝ) in 0..1, (B (wi + s • (wk - wi))) (wk - wi) ∧
        NumCore.pairF (wk - wi) (Φ wk - Φ wi) =
          ∫ (s : ℝ) in 0..1, NumCore.pairF (wk - wi) ((B (wi + s • (wk - wi))) (wk - wi))
```

CFD `CFDLean.Num.pair_production_integral` (module `CFDLean.Num.Production`):

```lean
∀ (κ : Type) [inst : Fintype κ] (Φ : (κ → ℝ) → κ → ℝ)
  (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] κ → ℝ) (wi wk : κ → ℝ),
  (∀ s ∈ Set.Icc 0 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) →
    ContinuousOn (fun s => (B (wi + s • (wk - wi))) (wk - wi)) (Set.Icc 0 1) →
      Φ wk - Φ wi = ∫ (s : ℝ) in 0..1, (B (wi + s • (wk - wi))) (wk - wi) ∧
        CFDLean.Num.pairF (wk - wi) (Φ wk - Φ wi) =
          ∫ (s : ℝ) in 0..1, CFDLean.Num.pairF (wk - wi) ((B (wi + s • (wk - wi))) (wk - wi))
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.0b: `CFDLean.Num.ofMeshData_closed`

JST `Paper1.Spec.P1_5_0b` (proof `Paper1.Proofs.p1_5_0b`):

```lean
∀ (n m : ℕ) (M : CFDLean.MedianDual.MeshData n m) (i : Fin n),
  M.Conforming → (∀ (o : M.Occurrence), M.faceCount (M.faceID o) = 1 → i ∉ M.faceID o) → (Paper1.ofMeshData M).Closed i
```

CFD `CFDLean.Num.ofMeshData_closed` (module `CFDLean.Num.Bridge`):

```lean
∀ (n m : ℕ) (M : CFDLean.MedianDual.MeshData n m) (i : Fin n),
  M.Conforming →
    (∀ (o : M.Occurrence), M.faceCount (M.faceID o) = 1 → i ∉ M.faceID o) → (CFDLean.Num.ofMeshData M).Closed i
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.6: `CFDLean.Num.dualFacets_grad`

JST `Paper1.Spec.P1_5_6` (proof `Paper1.Proofs.p1_5_6`):

```lean
(∀ (p : CFDLean.MedianDual.Points),
    0 < CFDLean.MedianDual.sixVolume p →
      (Paper1.simplexOfPoints p).Nondeg ∧
        (Paper1.simplexOfPoints p).vol = CFDLean.MedianDual.volume p ∧
          ∀ (i k : Fin 4),
            CFDLean.MedianDual.localInterface p i k =
              ((Paper1.simplexOfPoints p).vol / 4) •
                ((Paper1.simplexOfPoints p).grad k - (Paper1.simplexOfPoints p).grad i)) ∧
  ∀ (T : NumCore.Simplex 2),
    T.Nondeg → ∀ (i k : Fin 3), i ≠ k → Paper1.dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i)
```

CFD `CFDLean.Num.dualFacets_grad` (module `CFDLean.Num.Bridge`):

```lean
(∀ (p : CFDLean.MedianDual.Points),
    0 < CFDLean.MedianDual.sixVolume p →
      (CFDLean.Num.simplexOfPoints p).Nondeg ∧
        (CFDLean.Num.simplexOfPoints p).vol = CFDLean.MedianDual.volume p ∧
          ∀ (i k : Fin 4),
            CFDLean.MedianDual.localInterface p i k =
              ((CFDLean.Num.simplexOfPoints p).vol / 4) •
                ((CFDLean.Num.simplexOfPoints p).grad k - (CFDLean.Num.simplexOfPoints p).grad i)) ∧
  ∀ (T : CFDLean.Num.Simplex 2),
    T.Nondeg → ∀ (i k : Fin 3), i ≠ k → CFDLean.Num.dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i)
```

Identical after renaming: pretty yes, raw yes.

### MC-N.P1-5.7: `CFDLean.Num.ofMeshData_fv_galerkin`

JST `Paper1.Spec.P1_5_7` (proof `Paper1.Proofs.p1_5_7`):

```lean
∀ (n m : ℕ) (κ : Type) [inst : Fintype κ] (M : CFDLean.MedianDual.MeshData n m)
  (Fl : Fin m → Matrix κ (Fin 3) ℝ) (i : Fin n),
  (∑ t,
      ∑ a, ∑ b, if (M.vertex t) a = i then (Fl t).mulVec (CFDLean.MedianDual.localInterface (M.points t) a b) else 0) =
    (Paper1.ofMeshData M).galerkinRes Fl i
```

CFD `CFDLean.Num.ofMeshData_fv_galerkin` (module `CFDLean.Num.Bridge`):

```lean
∀ (n m : ℕ) (κ : Type) [inst : Fintype κ]
  (M : CFDLean.MedianDual.MeshData n m) (Fl : Fin m → Matrix κ (Fin 3) ℝ) (i : Fin n),
  (∑ t,
      ∑ a, ∑ b, if (M.vertex t) a = i then (Fl t).mulVec (CFDLean.MedianDual.localInterface (M.points t) a b) else 0) =
    (CFDLean.Num.ofMeshData M).galerkinRes Fl i
```

Identical after renaming: pretty yes, raw yes.
