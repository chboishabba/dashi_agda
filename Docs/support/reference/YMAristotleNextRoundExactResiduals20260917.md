# Yang–Mills Aristotle next-round exact residual brief — 2026-09-17

## Authority and scope

This brief is consumer-first. The supplied Aristotle archive has already paid the generic operator/spectral endpoint, literal finite-spacing SU(2) Wilson construction, fixed-spacing strong-coupling gap, graph-limit gap transport, and same-evolution gap transfer. Do not re-prove those layers.

The current outstanding physical normal form is

\[
\boxed{F_1+F_2+F_3+F_4}
\]

with CMP116/BIDI available as an alternative producer for \(F_1\).

No citation, status flag, synthetic model, `sorry`, `axiom`, `postulate`, or assumption-record field renamed as a theorem counts as payment.

## Already paid — do not redo

### Vacuum-sector spectral/resolvent endpoint

Use `RequestProject/YangMills/VacuumSectorSpectralGap.lean`:

- `VacuumGapDatum.eigenvalue_eq_zero_of_lt_gap`
- `VacuumGapDatum.exists_unique_solution_vacuumSector`
- `VacuumGapDatum.resolvent_bound_vacuumSector`

Given a genuine `VacuumGapDatum E`, these already produce eigenvalue exclusion, unique vacuum-sector solvability for every `lam < gap`, and

\[
\|\psi\|\le(\Delta-\lambda)^{-1}\|(H-\lambda)\psi\|.
\]

### Literal finite SU(2) Wilson theory

Use the existing lattice chain:

- `RequestProject/YangMills/Lattice/CompactHaar.lean`
- `.../Config.lean`
- `.../Wilson.lean`
- `.../TransferForm.lean`
- `.../SU2.lean`
- `.../SU2YangMills.lean`
- `.../GaugeInvariantSlice.lean`
- `.../FreeCoupling.lean`
- `.../StrongCoupling.lean`
- `.../PhysicalStrongCoupling.lean`

Canonical finite objects include `ymGibbs`, `ymVacuum`, `ymEnergyForm`, `ymHamiltonian`, and the gauge-invariant `ymPhysicalVacuum` / `ymPhysicalHamiltonian` surface.

Do not reconstruct `q_a` or `H_a`. The literal form is already the rescaled transfer form

\[
q_a=a^{-1}\left(1-\tfrac12(T+T^*)\right).
\]

Existing finite compiler:

```lean
def HasLatticeCoercivity (Δ : ℝ) (ha : 0 ≤ a) : Prop :=
  ∀ ψ : ymHilbert n beta, ⟪ymVacuum n beta, ψ⟫_ℂ = 0 →
    Δ * ‖ψ‖ ^ 2 ≤ ((ymEnergyForm n beta a ha).form ψ ψ).re

theorem lattice_massGap_of_coercivity {Δ : ℝ} (hΔ : 0 < Δ) (ha : 0 ≤ a)
    (hcoer : HasLatticeCoercivity n beta a Δ ha) :
    Clay.MassGapConclusion (ymHamiltonian n beta a ha) (ymVacuum n beta) Δ
```

Existing physical strong-coupling theorem:

```lean
theorem ym_phys_massGap_of_coupling_le {n : ℕ} (hn : 1 ≤ n) {beta a : ℝ} (ha : 0 < a)
    (hbeta : 64 * |beta| * ((n : ℝ) + 1) ^ 4 ≤ 1 / 10) :
    Clay.MassGapConclusion (ymPhysicalHamiltonian n beta a ha.le)
      (ymPhysicalVacuum n beta)
      (a⁻¹ * (2 - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4)) - 1) ^ 2
        - (Real.exp (2 * (32 * |beta| * ((n : ℝ) + 1) ^ 4))) ^ 2))
```

This is fixed-spacing/strong-coupling only. Do not promote it to the continuum trajectory.

### Generic continuum gap transport

Use `RequestProject/YangMills/ContinuumGapTransport.lean`.

Exact graph-limit predicate:

```lean
def IsVacuumGraphLimit (H : ℕ → E →ₗ.[ℂ] E) (vacn : ℕ → E)
    (Hinf : E →ₗ.[ℂ] E) (vac : E) : Prop :=
  ∀ ψ : Hinf.domain, ⟪vac, (ψ : E)⟫_ℂ = 0 →
    ∃ (a : ℕ → E) (ha : ∀ n, a n ∈ (H n).domain),
      (∀ n, ⟪vacn n, a n⟫_ℂ = 0) ∧ Tendsto a atTop (𝓝 (ψ : E)) ∧
        Tendsto (fun n => (H n) ⟨a n, ha n⟩) atTop (𝓝 (Hinf ψ))
```

Use:

- `hasVacuumFormGap_of_graphLimit`
- `continuumDatum`

`continuumDatum` consumes exactly:

```lean
(hgap : ∀ n, HasVacuumFormGap (H n) (vacn n) Δ)
(hlim : IsVacuumGraphLimit H vacn Hinf vac)
(hsa : IsSelfAdjoint Hinf)
(hmem : vac ∈ Hinf.domain)
(hunit : ‖vac‖ = 1)
(hground : Hinf ⟨vac, hmem⟩ = 0)
(hΔ : 0 < Δ)
```

and returns `VacuumGapDatum E`.

### Generic YM/OS same-object transfer

Use `RequestProject/YangMills/SameObjectGapTransfer.lean`:

```lean
def vacuumGapDatum_of_same_evolution {U V : ℝ → E → E} {S : Submodule ℂ E}
    {H₁ H₂ : E →ₗ.[ℂ] E} (hUV : U = V)
    (hc₁ : H₁.HasCore S) (hc₂ : H₂.HasCore S)
    (hg₁ : IsPMapEvolutionGenerator U S H₁) (hg₂ : IsPMapEvolutionGenerator V S H₂)
    (D : VacuumGapDatum E) (hD : D.op = H₁) : VacuumGapDatum E
```

Do not add another generator-uniqueness theorem.

---

# F1 — uniform physical coercivity on the actual continuum/RG trajectory

## Exact mathematical target

The literal finite form/Hamiltonian is already available. Prove a positive constant independent of cutoff and volume along the actual continuum trajectory:

\[
\boxed{
\exists\Delta>0\;\forall k,n,\psi\perp\Omega_{n,k},\quad
\Delta\|\psi\|^2\le\operatorname{Re}q_{n,k,\beta(k)}(\psi,\psi).
}
\]

Here the physical trajectory must be the one used for the continuum construction, with the relevant limits corresponding to volume \(n\to\infty\), cutoff/lattice spacing \(a_k\to0\), and weak bare coupling / \(\beta(k)\to\infty\) as required by the selected Wilson/RG normalization.

## Preferred theorem shape

Construct a theorem/package whose downstream projection is literally:

```lean
∃ Δ : ℝ, 0 < Δ ∧
  ∀ k,
    HasVacuumFormGap
      (physicalHam k)
      (physicalVacuum k)
      Δ
```

where `physicalHam k` and `physicalVacuum k` are definitionally or theorem-proven to be the literal lattice objects after the F2 carrier embedding.

### Forbidden shortcut

The existing `ym_phys_massGap_of_coupling_le` hypothesis

```lean
64 * |beta| * ((n : ℝ) + 1)^4 ≤ 1/10
```

shrinks in the wrong direction with volume and does not establish the physical continuum trajectory. Do not call it a uniform continuum gap.

## Alternative source/BIDI route for F1

If direct form coercivity is harder, use the already-built CMP116/BIDI stack to prove uniform clustering on the same physical Hamiltonian and feed the existing clustering-to-gap compiler. Do not rebuild the spectral implication.

---

# F2 — varying Hilbert spaces / common physical carrier

## Problem

The literal finite spaces vary:

\[
\mathcal H_{n,\beta}=L^2_{\rm gauge}(\mu_{n,\beta}),
\]

but `Clay.CutoffFamily` and `ContinuumGapTransport.IsVacuumGraphLimit` currently quantify a single `E`.

## Preferred route A: compatible isometric embeddings

Construct a common complete complex Hilbert space `Ecommon` and maps of the shape

```lean
J : ∀ k, Ecutoff k →ₗᵢ[ℂ] Ecommon
```

with proofs that:

1. the literal physical vacua map to the selected common-carrier vacua;
2. the literal physical Hamiltonians are intertwined on their domains;
3. inner products/norms and vacuum orthogonality are preserved;
4. the transported operators are the `H k` consumed by `IsVacuumGraphLimit`;
5. no post-hoc choice of `Ecommon`, `H k`, or vacuum erases the literal Wilson same-object identity.

## Route B if A is mathematically unnatural

Generalize the existing graph-limit theorem to varying Hilbert spaces in the Kuwae–Shioya/Mosco style, then prove the existing fixed-space theorem as a special case. Do this only if it genuinely reduces assumptions; do not create a second unused convergence framework.

### Acceptance target

At the end of F2 we must have a family usable directly by the F3 graph/Mosco theorem without an unproved equality between the literal finite Hamiltonian and the transported one.

---

# F3 — actual physical cutoff-to-continuum construction

## Required output

Using the literal Wilson family after F2, construct actual `Hinf` and `vac` and prove the exact fields required by `ContinuumGapTransport.continuumDatum`:

```lean
IsVacuumGraphLimit H vacn Hinf vac
IsSelfAdjoint Hinf
vac ∈ Hinf.domain
‖vac‖ = 1
Hinf ⟨vac, hmem⟩ = 0
```

and retain the same physical family at the measure/Schwinger level where needed.

The Agda counterpart is already normalized around
`BalabanVacuumOrthogonalMoscoRecoveryExact.VacuumOrthogonalRecoverySystem`; use that as a semantic cross-check, not as proof that the Lean physical family converges.

### Required same-family statements

Do not silently switch models between:

- Wilson cutoff measure,
- finite physical Hilbert/form/Hamiltonian,
- limiting measure/Schwinger family,
- limiting Hamiltonian/vacuum.

Every transition must retain an explicit same-object theorem.

---

# F4 — actual Yang–Mills / Osterwalder–Schrader same-object weld

## Exact consumer

Instantiate `SameObjectGapTransfer.vacuumGapDatum_of_same_evolution` on the actual F3 continuum Hamiltonian.

Produce:

```lean
S : Submodule ℂ Ecommon
Uym Uos : ℝ → Ecommon → Ecommon

hUV : Uym = Uos
hcYM : Hinf.HasCore S
hcOS : Hos.HasCore S
hgYM : IsPMapEvolutionGenerator Uym S Hinf
hgOS : IsPMapEvolutionGenerator Uos S Hos
```

where `Hos` is the Hamiltonian reconstructed from the same continuum Schwinger family produced by F3.

The decisive theorem is

\[
\boxed{U_\infty^{YM}=U^{OS}}
\]

for the actual theory, not `OSWeld.self` and not an equality obtained by defining both sides to be the same object.

Then call the existing same-evolution compiler; do not re-prove generator uniqueness.

---

# CMP116 alternate F1 producer — exact residual leaves

Do not ask for “CMP116” as one theorem. The existing
`RG/BalabanCMP116SourceTheorem.lean` compiler should be fed only the missing physical leaves.

The physical/source obligations to inhabit are:

```text
covariance_root_certificate
root_localization
gaussian_pushforward
wilson_hessian_identification
local_physical_activity_construction
spectator_support_subset
fluctuation_support_subset
activity_stronglyMeasurable
raw_pointwise_decay
amplitude_nonneg / amplitude_le_one
weight_nonneg
active_support_subset_omega
active_support_subset_skeleton
weight_domination
probability_law
holes_pairwise_disjoint
no_edges_between_holes
holes_nonempty
appendix_f_geometric_smallness
rooted_hsharp_remainder_identity
profile_constant_nonneg
hbar_nonneg
kappa_margin
kappa0_gt_one
time_decay_positive
half_budget
profile_bound
epsilon_positive
beta_flow_positive
coupling_positive
coupling_small
coupling_recursion
ir_bound
```

Then use:

```lean
balabanCMP116SourceTheorem_of_assumptions
```

and the existing M3/source/R387 pipeline. Do not rebuild resummation, UV iteration, source-to-covariance normalization, or clustering-to-gap mathematics.

The final spectral attachment should correspond to the Agda seam
`YMClayR387PhysicalMassGapCertificateExact.R387PhysicalSpectralInterpretation`:
R387 `NoPositiveSubgapMode` must be shown to mean the physical Hamiltonian's spectrum is above the exact same selected gap.

---

# Final acceptance theorem

The next round is complete only when the physical leaves above are consumed into one theorem with no unresolved Yang–Mills hypotheses, schematically:

```lean
theorem clayYangMillsMassGap_unconditional :
  RequestProject.YangMills.Clay.MassGapConclusion Hos Ω Δ
```

for the actual continuum theory, with `0 < Δ` and `Hos` the OS-reconstructed Hamiltonian same-object with the F3 physical continuum Hamiltonian.

The theorem must obtain its finite gap from F1 (direct coercivity or CMP116/clustering), its common carrier from F2, its continuum datum from F3, and its OS transfer from F4.

## Verification gate

Required before any completion claim:

1. `lake build RequestProject` exits 0.
2. Focused Yang–Mills roots also build.
3. Search the new tranche for `sorry`, `axiom`, `postulate`, `@[implemented_by]` — none permitted.
4. `#print axioms` every headline theorem; only the project-accepted foundational Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) may remain.
5. Report exact theorem names and any remaining hypotheses verbatim. If any F1–F4 physical hypothesis remains, do not claim the Clay theorem.

## Agda synchronization

The Agda residual owners corresponding to this brief are:

- `YMClayLiteralSU2LatticeDonorExact`
- `YMClayVacuumSectorSpectralGapParityExact`
- `YMClayR387PhysicalMassGapCertificateExact`
- `YMClayOutstandingPhysicalFrontierExact`
- `YMClayCanonicalMassGapConclusionExact`

Use them as the authority map for what is already paid versus still physical. Lean theorem success does not silently become Agda kernel certification, and Agda source wrappers do not create physical truth.
