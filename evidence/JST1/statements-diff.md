# Statement comparison, v4.19 to v4.36

Inputs: `evidence/statements-v4.19.txt` (Lean v4.19, Mathlib c44e0c8) and `evidence/statements-v4.36.txt` (Lean v4.36.0, Mathlib fc4f59e), both produced by `lake env lean scripts/DumpStmts.lean`, which prints the value of each of the 92 bound statement definitions `Paper1.Spec.P*`. Texts are compared after joining continuation lines and collapsing runs of whitespace, so changes of line breaking alone do not count as differences.

- statements: 92
- identical: 74
- differing: 18

| Class | Count |
|---|---|
| mathlib-rename | 0 |
| notation | 1 |
| pretty-printer | 17 |
| other | 0 |

The frozen statement files are compiled with `set_option cleanup.letToHave false` (see `evidence/frozen-edits.patch`). Without it, Lean v4.36 rewrites every non-dependent `let` in a definition body to `have`, and the 24 statements that contain `let` would print `have` instead (a test dump without the option showed this). With the option, all 24 print `let` exactly as in v4.19.

One identical string rests on a changed Mathlib definition: `Paper1.Spec.P2_7_2` uses `Matrix.PosSemidef`. Mathlib now defines it for arbitrary index types through finitely supported vectors (`x : n →₀ R`); for the finite index `Fin d` used here, `Matrix.posSemidef_iff_dotProduct_mulVec` states that it is equivalent to the old definition (Hermitian and `0 ≤ star x ⬝ᵥ M *ᵥ x` for all `x`). The proof `Paper1.Proofs.Dg7.outer_psd` now goes through that lemma.

## Differing statements

### `Paper1.Spec.P1_2_6`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι S κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (u : ι → S) (ut : ι → κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι) (b : ι → κ → ℝ), (∀ (i k : ι), n k i = -n i k) → (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = Fec b a y) → (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (i k : ι), lam k i = lam i k) → (∀ (i k : ι), eps2 k i = eps2 i k) → (∀ (i k : ι), eps4 k i = eps4 i k) → let L := fun i => ∑ k ∈ Nstar i, (ut k - ut i); let F := fun i k => Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k)); (∀ (i k : ι), F k i = -F i k) ∧ ∑ i, (-∑ k, F i k - b i) = -∑ i, b i
```
New (v4.36):
```
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (u : ι → S) (ut : ι → κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι) (b : ι → κ → ℝ), (∀ (i k : ι), n k i = -n i k) → (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = Fec b a y) → (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (i k : ι), lam k i = lam i k) → (∀ (i k : ι), eps2 k i = eps2 i k) → (∀ (i k : ι), eps4 k i = eps4 i k) → let L := fun i => ∑ k ∈ Nstar i, (ut k - ut i); let F := fun i k => Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k)); (∀ (i k : ι), F k i = -F i k) ∧ ∑ i, (-∑ k, F i k - b i) = -∑ i, b i
```

### `Paper1.Spec.P1_2_7`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι S κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (U : S) (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι), (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (y : NumCore.Vec d), Fec U U y = phys U y) → let beta := fun i => -∑ k, n i k; let L := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0); let F := fun i k => Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k)); ∀ (i : ι), -∑ k, F i k - phys U (beta i) = 0
```
New (v4.36):
```
∀ (ι S κ : Type) [inst : Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (n : ι → ι → NumCore.Vec d) (U : S) (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ) (Nstar : ι → Finset ι), (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (y : NumCore.Vec d), Fec U U y = phys U y) → let beta := fun i => -∑ k, n i k; let L := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0); let F := fun i k => Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k)); ∀ (i : ι), -∑ k, F i k - phys U (beta i) = 0
```

### `Paper1.Spec.P1_3_3`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι σ κ : Type) [inst : Fintype ι] [inst : Fintype σ] (d : ℕ) (ω : σ → ℝ) (χ : σ → ι → ι → Bool) (n e vb : ι → ι → NumCore.Vec d) (cb : ι → ι → ℝ) (Lam : ι → ℝ) (a : ℝ) (D : κ → ℝ) (i k : ι), (∀ (s : σ), 0 ≤ ω s) → 0 < Paper1.piShare ω χ i k → 0 < Paper1.lamHat (vb i k) (cb i k) (e i k) (n i k) → 0 < Lam i → 0 < Lam k → (∑ s, ω s • if χ s i k = Bool.true then Paper1.coefOn vb cb e Lam a (fun j l => Paper1.nSplit ω χ n s j l) i k • D else 0) = (Paper1.piShare ω χ i k ^ a * Paper1.coefOn vb cb e Lam a n i k) • D
```
New (v4.36):
```
∀ (ι σ κ : Type) [Fintype ι] [inst : Fintype σ] (d : ℕ) (ω : σ → ℝ) (χ : σ → ι → ι → Bool) (n e vb : ι → ι → NumCore.Vec d) (cb : ι → ι → ℝ) (Lam : ι → ℝ) (a : ℝ) (D : κ → ℝ) (i k : ι), (∀ (s : σ), 0 ≤ ω s) → 0 < Paper1.piShare ω χ i k → 0 < Paper1.lamHat (vb i k) (cb i k) (e i k) (n i k) → 0 < Lam i → 0 < Lam k → (∑ s, ω s • if χ s i k = Bool.true then Paper1.coefOn vb cb e Lam a (fun j l => Paper1.nSplit ω χ n s j l) i k • D else 0) = (Paper1.piShare ω χ i k ^ a * Paper1.coefOn vb cb e Lam a n i k) • D
```

### `Paper1.Spec.P1_5_0a`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (i : ι), M.Valid → M.FacetPaired i → M.Closed i
```
New (v4.36):
```
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (i : ι), M.Valid → M.FacetPaired i → M.Closed i
```

### `Paper1.Spec.P1_5_2`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d), M.Valid → (∀ (i k : ι), i ≠ k → NumCore.dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧ ∀ (i k : ι), i ≠ k → (∃ T a b, (M.vert T) a = i ∧ (M.vert T) b = k ∧ 0 < M.ω T) → 0 < M.mu i k ∧ (∃ t, 0 < t ∧ M.nu i k = t • M.e i k) ∧ NumCore.len (M.nu i k) = NumCore.dot (M.n i k) (M.e i k) / NumCore.len (M.e i k)
```
New (v4.36):
```
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d), M.Valid → (∀ (i k : ι), i ≠ k → NumCore.dot (M.n i k) (M.e i k) = 2 * M.mu i k) ∧ ∀ (i k : ι), i ≠ k → (∃ T a b, (M.vert T) a = i ∧ (M.vert T) b = k ∧ 0 < M.ω T) → 0 < M.mu i k ∧ (∃ t, 0 < t ∧ M.nu i k = t • M.e i k) ∧ NumCore.len (M.nu i k) = NumCore.dot (M.n i k) (M.e i k) / NumCore.len (M.e i k)
```

### `Paper1.Spec.P1_5_5`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (S : C → ι → ι → NumCore.Vec d) (Fl : C → Matrix κ (Fin d) ℝ), (∀ (T : C) (a b : Fin (d + 1)), S T ((M.vert T) a) ((M.vert T) b) = M.m T • (M.g T b - M.g T a)) → ∀ (i : ι), M.fvRes Fl S i = M.galerkinRes Fl i
```
New (v4.36):
```
∀ (ι C κ : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (S : C → ι → ι → NumCore.Vec d) (Fl : C → Matrix κ (Fin d) ℝ), (∀ (T : C) (a b : Fin (d + 1)), S T ((M.vert T) a) ((M.vert T) b) = M.m T • (M.g T b - M.g T a)) → ∀ (i : ι), M.fvRes Fl S i = M.galerkinRes Fl i
```

### `Paper1.Spec.P1_5_8`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : Fintype κ] (M : NumCore.WMesh ι C 2) (Fl : C → Matrix κ (Fin 2) ℝ) (i : ι), M.Valid → (∑ T, ∑ a, ∑ b, if (M.vert T) a = i ∧ b ≠ a then M.ω T • (Fl T).mulVec (Paper1.dualFacet2 (M.simplex T) a b) else 0) = M.galerkinRes Fl i
```
New (v4.36):
```
∀ (ι C κ : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : Fintype κ] (M : NumCore.WMesh ι C 2) (Fl : C → Matrix κ (Fin 2) ℝ) (i : ι), M.Valid → (∑ T, ∑ a, ∑ b, if (M.vert T) a = i ∧ b ≠ a then M.ω T • (Fl T).mulVec (Paper1.dualFacet2 (M.simplex T) a b) else 0) = M.galerkinRes Fl i
```

### `Paper1.Spec.P2_6_3`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧ (∀ (i k : ι), M.B i k = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p else 0) ∧ ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i
```
New (v4.36):
```
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧ (∀ (i k : ι), M.B i k = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p else 0) ∧ ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i
```

### `Paper1.Spec.P2_6_4`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι κ : Type) [inst : Fintype ι] [inst_1 : Fintype κ] (d : ℕ) (c B : ι → ι → NumCore.Vec d) (β : ι → NumCore.Vec d) (F : ι → Matrix κ (Fin d) ℝ), (∀ (i : ι), ∑ k, c i k = 0) → (∀ (k : ι), ∑ i, c i k = β k) → (∀ (i : ι), ∑ k, B i k = β i) → let n := fun i k => c i k - c k i; let s := fun i k => (1 / 2) • (c i k + c k i - B i k); ∀ (i : ι), ∑ k, ((1 / 2) • (F i + F k)).mulVec (n i k) + ∑ k, (F k - F i).mulVec (s i k) + (1 / 2) • (∑ k, (F k).mulVec (B i k) + (F i).mulVec (β i)) = ∑ k, (F k).mulVec (c i k)
```
New (v4.36):
```
∀ (ι κ : Type) [inst : Fintype ι] [Fintype κ] (d : ℕ) (c B : ι → ι → NumCore.Vec d) (β : ι → NumCore.Vec d) (F : ι → Matrix κ (Fin d) ℝ), (∀ (i : ι), ∑ k, c i k = 0) → (∀ (k : ι), ∑ i, c i k = β k) → (∀ (i : ι), ∑ k, B i k = β i) → let n := fun i k => c i k - c k i; let s := fun i k => (1 / 2) • (c i k + c k i - B i k); ∀ (i : ι), ∑ k, ((1 / 2) • (F i + F k)).mulVec (n i k) + ∑ k, (F k - F i).mulVec (s i k) + (1 / 2) • (∑ k, (F k).mulVec (B i k) + (F i).mulVec (β i)) = ∑ k, (F k).mulVec (c i k)
```

### `Paper1.Spec.P2_6_5b`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] [inst_3 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (F : ι → Matrix κ (Fin d) ℝ), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (i : ι), ∑ k, (F k).mulVec ((1 / 2) • (M.B i k + if i = k then M.beta i else 0)) = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then ∑ j ∈ M.facetNodes p, Paper1.Spec.stdWeight d i j • (F j).mulVec (M.areaVec p) else 0) ∧ ∀ (i j : ι), i ≠ j → Paper1.Spec.stdWeight d i i = (↑d + 3) * Paper1.Spec.stdWeight d i j
```
New (v4.36):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] [Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (F : ι → Matrix κ (Fin d) ℝ), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (i : ι), ∑ k, (F k).mulVec ((1 / 2) • (M.B i k + if i = k then M.beta i else 0)) = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then ∑ j ∈ M.facetNodes p, Paper1.Spec.stdWeight d i j • (F j).mulVec (M.areaVec p) else 0) ∧ ∀ (i j : ι), i ≠ j → Paper1.Spec.stdWeight d i i = (↑d + 3) * Paper1.Spec.stdWeight d i j
```

### `Paper1.Spec.P2_6_7`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] [inst_3 : Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i → ∑ k, ((1 / 2) • (F i + F k)).mulVec (M.n i k) = ∑ k, (F k).mulVec (M.c i k) ∧ ∑ k, (F k).mulVec (M.c i k) = ∑ T, ∑ a, if (M.vert T) a = i then (M.ω T * M.m T) • ∑ b, (F ((M.vert T) b)).mulVec (M.g T b) else 0
```
New (v4.36):
```
∀ (ι C κ : Type) [inst : Fintype ι] [inst_1 : DecidableEq ι] [inst_2 : Fintype C] [Fintype κ] (d : ℕ) (M : NumCore.WMesh ι C d) (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i → ∑ k, ((1 / 2) • (F i + F k)).mulVec (M.n i k) = ∑ k, (F k).mulVec (M.c i k) ∧ ∑ k, (F k).mulVec (M.c i k) = ∑ T, ∑ a, if (M.vert T) a = i then (M.ω T * M.m T) • ∑ b, (F ((M.vert T) b)).mulVec (M.g T b) else 0
```

### `Paper1.Spec.P2_8_2`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [inst_2 : Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ) (N : Q → NumCore.Vec d) (n : ι → ι → NumCore.Vec d), (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (y : NumCore.Vec d), Fec U U y = phys U y) → (∀ (q : Q), ∑ k, φ q k = 1) → (∀ (i : ι), ∑ q, φ q i • N q = -∑ k, n i k) → let b := fun i => ∑ q, φ q i • (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q)); ∀ (i : ι), -∑ k, Fec U U (n i k) - b i = 0
```
New (v4.36):
```
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (phys : S → NumCore.Vec d → κ → ℝ) (U : S) (φ : Q → ι → ℝ) (N : Q → NumCore.Vec d) (n : ι → ι → NumCore.Vec d), (∀ (a b : S), IsLinearMap ℝ (Fec a b)) → (∀ (y : NumCore.Vec d), Fec U U y = phys U y) → (∀ (q : Q), ∑ k, φ q k = 1) → (∀ (i : ι), ∑ q, φ q i • N q = -∑ k, n i k) → let b := fun i => ∑ q, φ q i • (Fec U U (N q) - ∑ k, φ q k • Fec U U (N q) + phys U (N q)); ∀ (i : ι), -∑ k, Fec U U (n i k) - b i = 0
```

### `Paper1.Spec.P2_8_3`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [inst_2 : Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → NumCore.Vec d) (ut : Q → S), (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = ((1 / 2) • (Fl a + Fl b)).mulVec y) → (∀ (q : Q), Fl (ut q) = ∑ k, φ q k • Fl (u k)) → (∀ (q : Q), ∑ k, φ q k = 1) → let beta := fun i => ∑ q, φ q i • N q; let b := fun i => ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q)); ∀ (i : ι), b i = (1 / 2) • ((Fl (u i)).mulVec (beta i) + ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q))
```
New (v4.36):
```
∀ (ι Q S κ : Type) [inst : Fintype ι] [inst_1 : Fintype Q] [Fintype κ] (d : ℕ) (Fec : S → S → NumCore.Vec d → κ → ℝ) (Fl : S → Matrix κ (Fin d) ℝ) (u : ι → S) (φ : Q → ι → ℝ) (N : Q → NumCore.Vec d) (ut : Q → S), (∀ (a b : S) (y : NumCore.Vec d), Fec a b y = ((1 / 2) • (Fl a + Fl b)).mulVec y) → (∀ (q : Q), Fl (ut q) = ∑ k, φ q k • Fl (u k)) → (∀ (q : Q), ∑ k, φ q k = 1) → let beta := fun i => ∑ q, φ q i • N q; let b := fun i => ∑ q, φ q i • (Fec (u i) (ut q) (N q) - ∑ k, φ q k • Fec (ut q) (u k) (N q) + (Fl (ut q)).mulVec (N q)); ∀ (i : ι), b i = (1 / 2) • ((Fl (u i)).mulVec (beta i) + ∑ k, (Fl (u k)).mulVec (∑ q, (φ q i * φ q k) • N q))
```

### `Paper1.Spec.P2_8_4`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C Q : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : DecidableEq C] [inst_3 : Fintype Q] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (q : Q), bd (fq q) = Bool.true) → (∀ (q : Q), ∀ k ∉ M.facetNodes (fq q), φ q k = 0) → (∀ (p : C × Fin (d + 1)), bd p = Bool.true → ∀ i ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / ↑d) → (∀ (p : C × Fin (d + 1)), bd p = Bool.true → ∀ i ∈ M.facetNodes p, ∀ k ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) = (1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) → let N := fun q => aq q • M.areaVec (fq q); (∀ (i : ι), ∑ q, φ q i • N q = M.beta i) ∧ ∀ (i k : ι), ∑ q, (φ q i * φ q k) • N q = M.B i k
```
New (v4.36):
```
∀ (ι C Q : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] [inst_2 : DecidableEq C] [inst_3 : Fintype Q] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool) (fq : Q → C × Fin (d + 1)) (aq : Q → ℝ) (φ : Q → ι → ℝ), M.Valid → 1 ≤ d → M.Conforming bd → (∀ (q : Q), bd (fq q) = Bool.true) → (∀ (q : Q), ∀ k ∉ M.facetNodes (fq q), φ q k = 0) → (∀ (p : C × Fin (d + 1)), bd p = Bool.true → ∀ i ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i else 0) = 1 / ↑d) → (∀ (p : C × Fin (d + 1)), bd p = Bool.true → ∀ i ∈ M.facetNodes p, ∀ k ∈ M.facetNodes p, (∑ q, if fq q = p then aq q * φ q i * φ q k else 0) = (1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) → let N := fun q => aq q • M.areaVec (fq q); (∀ (i : ι), ∑ q, φ q i • N q = M.beta i) ∧ ∀ (i k : ι), ∑ q, (φ q i * φ q k) • N q = M.B i k
```

### `Paper1.Spec.P3_11_1`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → (M.Conforming bd → M.FacetBalanced bd) ∧ (M.FacetBalanced bd → (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧ (∀ (i k : ι), M.B i k = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p else 0) ∧ ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i)
```
New (v4.36):
```
∀ (ι C : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype C] (d : ℕ) (M : NumCore.WMesh ι C d) (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d → (M.Conforming bd → M.FacetBalanced bd) ∧ (M.FacetBalanced bd → (∀ (i : ι), M.beta i = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p then (1 / ↑d) • M.areaVec p else 0) ∧ (∀ (i k : ι), M.B i k = ∑ p, if bd p = Bool.true ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then ((1 + if i = k then 1 else 0) / (↑d * (↑d + 1))) • M.areaVec p else 0) ∧ ∀ (i : ι), (∀ (p : C × Fin (d + 1)), bd p = Bool.true → i ∉ M.facetNodes p) → M.Closed i)
```

### `Paper1.Spec.P3_13_1`: notation

Mathlib interval-integral notation now prints `∫ s in 0..1` instead of `∫ s in 0 ..1`; the term is `intervalIntegral _ 0 1 volume` in both.

Old (v4.19):
```
∀ (κ : Type) [inst : Fintype κ] (Φ : (κ → ℝ) → κ → ℝ) (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] κ → ℝ) (wi wk : κ → ℝ), (∀ s ∈ Set.Icc 0 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) → ContinuousOn (fun s => (B (wi + s • (wk - wi))) (wk - wi)) (Set.Icc 0 1) → Φ wk - Φ wi = ∫ (s : ℝ) in 0 ..1, (B (wi + s • (wk - wi))) (wk - wi) ∧ NumCore.pairF (wk - wi) (Φ wk - Φ wi) = ∫ (s : ℝ) in 0 ..1, NumCore.pairF (wk - wi) ((B (wi + s • (wk - wi))) (wk - wi))
```
New (v4.36):
```
∀ (κ : Type) [inst : Fintype κ] (Φ : (κ → ℝ) → κ → ℝ) (B : (κ → ℝ) → (κ → ℝ) →L[ℝ] κ → ℝ) (wi wk : κ → ℝ), (∀ s ∈ Set.Icc 0 1, HasFDerivAt Φ (B (wi + s • (wk - wi))) (wi + s • (wk - wi))) → ContinuousOn (fun s => (B (wi + s • (wk - wi))) (wk - wi)) (Set.Icc 0 1) → Φ wk - Φ wi = ∫ (s : ℝ) in 0..1, (B (wi + s • (wk - wi))) (wk - wi) ∧ NumCore.pairF (wk - wi) (Φ wk - Φ wi) = ∫ (s : ℝ) in 0..1, NumCore.pairF (wk - wi) ((B (wi + s • (wk - wi))) (wk - wi))
```

### `Paper1.Spec.P3_14_2`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι C Q : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst : Fintype C] [inst : Fintype Q] (d : ℕ) (S : Paper1.Scheme.Data ι C Q d) (slip : Q → Bool) (ug : Q → Paper1.State d), (∀ (q : Q), Paper1.Admissible S.g (S.ut q)) → (∀ (q : Q), slip q = Bool.true → S.Fs q = Paper1.pressFlux S.g (S.ut q) (S.N q)) → (∀ (q : Q), slip q = Bool.false → NumCore.pairF (Paper1.entropyVars S.g (ug q) - Paper1.entropyVars S.g (S.ut q)) (S.Fs q) ≤ NumCore.dot (Paper1.fluxPot (ug q) - Paper1.fluxPot (S.ut q)) (S.N q)) → Paper1.Scheme.Bterm S ≤ ∑ q, if slip q = Bool.true then 0 else NumCore.dot (Paper1.fluxPot (ug q)) (S.N q) - NumCore.pairF (Paper1.entropyVars S.g (ug q)) (S.Fs q)
```
New (v4.36):
```
∀ (ι C Q : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [inst : Fintype Q] (d : ℕ) (S : Paper1.Scheme.Data ι C Q d) (slip : Q → Bool) (ug : Q → Paper1.State d), (∀ (q : Q), Paper1.Admissible S.g (S.ut q)) → (∀ (q : Q), slip q = Bool.true → S.Fs q = Paper1.pressFlux S.g (S.ut q) (S.N q)) → (∀ (q : Q), slip q = Bool.false → NumCore.pairF (Paper1.entropyVars S.g (ug q) - Paper1.entropyVars S.g (S.ut q)) (S.Fs q) ≤ NumCore.dot (Paper1.fluxPot (ug q) - Paper1.fluxPot (S.ut q)) (S.N q)) → Paper1.Scheme.Bterm S ≤ ∑ q, if slip q = Bool.true then 0 else NumCore.dot (Paper1.fluxPot (ug q)) (S.N q) - NumCore.pairF (Paper1.entropyVars S.g (ug q)) (S.Fs q)
```

### `Paper1.Spec.P3_11_8`: pretty-printer

only the names of instance binders differ: v4.36 prints an unused instance binder anonymously (`[Fintype κ]` instead of `[inst_2 : Fintype κ]`); binder names are not part of the term (de Bruijn indices), types and order are unchanged.

Old (v4.19):
```
∀ (ι Cl : Type) [inst : Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype Cl] [inst_2 : DecidableEq Cl] (M : Paper1.Mixed.Mesh ι Cl) (bdTris : Finset (Finset ι)), M.Affine → M.Conform bdTris → M.toW.Valid ∧ M.toW.FacetBalanced fun p => Decidable.decide (M.toW.facetNodes p ∈ bdTris)
```
New (v4.36):
```
∀ (ι Cl : Type) [Fintype ι] [inst : DecidableEq ι] [inst_1 : Fintype Cl] [DecidableEq Cl] (M : Paper1.Mixed.Mesh ι Cl) (bdTris : Finset (Finset ι)), M.Affine → M.Conform bdTris → M.toW.Valid ∧ M.toW.FacetBalanced fun p => Decidable.decide (M.toW.facetNodes p ∈ bdTris)
```

## Raw comparison (pp.notation false, pp.coercions false, pp.fullNames) and the Mathlib Set refactor

A second dump without notation and coercions (`*-raw-v4.19.txt` / `*-raw-v4.36.txt`, script in `scripts/`) shows the
head constants. Besides the items above, it shows changes caused by the Mathlib refactor that makes `Set α` a
structure (Mathlib fc4f59e `Mathlib/Data/Set/Defs.lean`: `structure Set (α) where ofPred :: Mem`; `LE (Set α)` is
`Set.Subset`; `Max (Set α)` is `Set.union`; Finset `≤` comes from `PartialOrder.ofSetLike`, the subset relation):
`setOf` becomes `Set.ofPred`, Finset `⊆` is elaborated as `LE.le`, Set `∪` as `Max.max`. The printed (notation)
strings are equal and the meaning is the same. Affected: CFD `isOpen_admissible`, `face_membership`,
`roe_convective_tangent_span`; JST `P2_10_3`. The same refactor forces `upperRegion x` to `x ∈ upperRegion`
(a `Set` is no longer a function). Fin casts: `Fin.instNatCast` (v4.19, `Fin.ofNat'`) and core
`Fin.NatCast.instNatCast` (v4.36, `Fin.ofNat`) both give `⟨a % n, _⟩`. AI statement review of 2026-11-25: no
promised statement or definition changed meaning.
