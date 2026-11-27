# FVNA proposal review 1

The repository owner supplied the following external review of `specifications/FV1D-nonuniform-array-proposal.md` at
revision `80143b893a3cc45f9a8776f154274bc0686ea149` ([PR #44](https://github.com/rois1995/CFD_Lean/pull/44)).

> Mandatory changes
> 1. FVNA-F is too broad as written. The phrase
> “For every FVA model instance, the first-order array kernel over the reals represents FV1D.Nonuniform.firstOrderStep ...”
>
> is not valid for an arbitrary Exec.FV1D.Model ℝ S.
>
> Model is only an executable record containing arbitrary operations:
> add   : S → S → S
> sub   : S → S → S
> scale : ℝ → S → S
> flux  : S → S
> speed : S → S → ℝ
>
> with no laws saying that add, sub, and scale are the actual AddCommGroup/`Module ℝ` operations used by mathematical FVN. The existing FVA refinement handles this correctly: its generic exact_step theorem constructs the particular compatible model
> ⟨(· + ·), (· - ·), (· • ·), F, a⟩
>
> and then separately proves that the Burgers and Euler executable models equal such compatible models.
>
> FVNA-F should therefore say one of:
> - generically: for an FVA model whose state arithmetic is exactly the mathematical +, -, and •, with flux = F and speed = a; or
> - more simply, bind refinement for the concrete Burgers and Euler real models, while keeping the generic stencil lemma supporting.
> Do not quantify the mathematical refinement over an unconstrained Model ℝ S.
>
> This same restriction should be reflected in any generic conservation-transfer wording in FVNA-T.
> 2. FVNA-T(c) is missing the initial-bounds hypothesis. It currently says that for a limited L, mesh ratio, dt ≥ 0, and 8 dt max(|m|,|M|) ≤ w_i, n steps keep [m,M] and decrease TV.
>
> The frozen FVN-MB theorem additionally requires the initial field to satisfy m ≤ u_i ≤ M for every cell. The array transfer must explicitly require the corresponding EntriesBetween m M u (or equivalent representation hypothesis).
>
> Without that assumption, the claim is false: the timestep restriction cannot force an initially out-of-bounds state into [m,M].
> 3. Clarify FVNA-T(a) by state type. “The width-weighted sum ∑ w[i] * u[i] is kept by every kernel” is literally scalar notation, while the shared first-order kernel also covers Euler states.
> The intended theorem is sound, but the contract should distinguish:
> - Burgers/scalar: preservation of ∑_i w_i u_i;
> - generic module state: preservation of ∑_i w_i • U_i, when using the compatible mathematical model;
> - Euler: equivalently, componentwise weighted conservation of density, momentum, and energy.
> This is mostly a statement-precision issue, but because FVNA-T is a frozen result ID, I would correct it before freezing.
> Non-blocking suggestions
> - The proposed array rescaling is correct: 2w_i/(w_{i-1}+w_i) = w_i/δ_{i-1}, 2w_i/(w_i+w_{i+1}) = w_i/δ_i. The periodic indexing is also aligned correctly: the right trace at face i uses the slope of i+1, whose backward rescaling uses exactly the same face pair w_i, w_{i+1}. I would make this correspondence an explicit refinement lemma rather than repeatedly unfolding modular indexing.
> - FVNA-U is well chosen. Equal widths reduce both rescaling factors exactly to one over ℝ, so the nonuniform MUSCL kernel should reduce to E0c without requiring a limiter-specific argument.
> - For FVNA-T(c), keep L ≠ .none explicit rather than relying only on L.isLimited = true. The existing refinement library already provides Limiter.slopeBounded L hL and L.theta; reusing that theorem boundary will make the transfer cleaner.
> - It would be useful for FVNA-T(a) to distinguish one-step conservation from repeated SSP conservation in the result map. Both are true: Forward Euler conserves because of flux cancellation, and SSPRK2/3 preserve the same linear weighted invariant because their exact-real affine coefficients sum to one. This need not become separate result IDs.
> - The controls are appropriate. In particular, retaining the nonuniform FVN-BC case is valuable because it detects using the correct state index and width index together, which a uniform-grid comparison cannot test.
> - The decision to leave the driver unchanged is correct. FVNA should establish the executable numerical layer before the general fv1d driver consumes it.
> Independent external reviewer conclusion
> DO NOT FREEZE YET — MANDATORY STATEMENT CHANGES REQUIRED.
>
> I reviewed proposal revision:
>
> 80143b893a3cc45f9a8776f154274bc0686ea149
>
> The proposed kernels themselves are architecturally sound. The nonuniform array differences match FVN, the periodic face/width alignment is correct including the seam, the uniform reduction to FVA/E0c is valid over exact real arithmetic, and transferring the FVN stability results to represented arrays is the right proof strategy.
>
> However, I would not freeze the four result IDs as currently worded because:
> 1. FVNA-F incorrectly quantifies refinement over arbitrary lawless FVA Model records;
> 2. FVNA-T(c) omits the necessary initial [m,M] hypothesis;
> 3. FVNA-T(a) should state the generic/module versus scalar/Euler conservation quantity precisely.
> After those statement corrections, I would expect to recommend freezing FVNA-F, FVNA-M, FVNA-U, and FVNA-T without changing the proposed kernel formulas or milestone architecture.

## Changes made in response

1. FVNA-F now binds refinement only for the concrete Burgers and Euler real models. The shared stencil lemma is
   stated for the compatible model `⟨(· + ·), (· - ·), (· • ·), F, a⟩` and stays supporting.
2. FVNA-T (b) and (c) require every entry of `u` in `[m, M]` (`EntriesBetween m M u`). FVNA-T (c) says `L ≠ none`.
3. FVNA-T (a) distinguishes Burgers (`∑ w[i] * u[i]`, every kernel) from Euler (first-order kernel, componentwise
   weighted density, momentum and energy). The proposal notes one-step conservation by flux cancellation and SSP
   conservation by coefficients summing to one.

The face and width alignment is named as one explicit refinement lemma. The kernel formulas and the architecture are
unchanged.
