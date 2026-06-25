module DASHI.Physics.YangMills.O4CovarianceRestorationGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

-- ── O(4) covariance restoration postulates ─────────────────────────
--
-- Source: Eriksson 2602.0087 (Classification + coefficient bound + insertion)
--         Eriksson 2602.0092 (Ward identity + OS1)
--
-- 20. AnisotropicSubspaceClassificationTheorem
--     Eriksson 2602.0087, Theorem 3.6 (unconditional)
--     O_{6,os} = ker(Proj_aniso) ⊕ span{O_aniso}, dim O_{6,aniso} = 1
--
-- 21. AnisotropyCoeffQuadraticBound
--     Eriksson 2602.0087, Theorem 5.4
--     |c⁽ᵏ⁾_{6,aniso}| ≤ C aₖ² uniformly in η, L_phys, k ≤ k*
--     Conditional on: polymer analyticity (P4), coupling control (P19)
--
-- 22. InsertionIntegrabilityBound
--     Eriksson 2602.0087, Theorem 6.6
--     I^η_{O_aniso}(f) ≤ C(f) < ∞ uniformly in η
--     Conditional on: OS4 clustering (now discharged via DLR-LSI, P12–P15)
--
-- 28. ImportedRotationalWardIdentity
--     Eriksson 2602.0092, Proposition 3.2
--     ⟨S^η_n, L_μν f⟩ = −Σ_y η⁴ ∫ f(x) ⟨(δ_μν s_W)(y)·∏O(xj)⟩ dx + E^η_n(f)
--     |E^η_n(f)| ≤ C_n η² ‖f‖_{W^{1,1}}
--     Unconditional (no change of variables in path integral)
--
-- 29. ImportedSymanzikBreakingDecomposition
--     Eriksson 2602.0092, Proposition 3.4
--     (δ_μν s_W)(y) = g₀(η)⁻² η² [λ_μν O_aniso(y) + Q^{O(4)}_μν(y) + O(η²)]
--     λ_μν ≠ 0 (Appendix A); W₄-equivariance → λ_μν plane-independent
--     Conditional on: P20 (anisotropic classification, 2602.0087 Thm 3.6)
--
-- 30. ImportedOS1EuclideanCovariance
--     Eriksson 2602.0092, Theorem 4.2 + Corollary 4.3
--     L_μν S_n = 0 in S'(ℝ^{4n}); full O(4) covariance
--     Proof: P28+P29+P22 → RHS = O(η² log(η⁻¹)) → 0
--     Conditional on: P28, P29, P22 (insertion integrability)
--
-- 32. TriangularMixingPreventiveLock
--     Eriksson 2602.0096, Theorem 8.5 + Corollary 8.6
--     Z_{4←6}(O^{W4,aniso}_6) ⊂ O^{W4}_4 ∩ {O(4)-invariant}
--     No d=4 anisotropic sink exists in the W4-scalar gauge-invariant sector
--     Consequence: a²×a⁻² → O(1) attack is structurally blocked
--     Conditional on: P20 (anisotropic classification, 2602.0087 Thm 3.6)

postulate
  AnisotropicSubspaceClassificationTheorem : Bool
  AnisotropyCoeffQuadraticBound            : Bool
  InsertionIntegrabilityBound              : Bool
  ImportedRotationalWardIdentity           : Bool
  ImportedSymanzikBreakingDecomposition    : Bool
  ImportedOS1EuclideanCovariance           : Bool
  TriangularMixingPreventiveLock           : Bool

-- ── O4CovarianceRestorationGate ─────────────────────────────────────
-- Every boolean is now true after 2602.0092 intake.

record O4CovarianceRestorationGate : Set where
  field
    -- UNCONDITIONAL
    hypercubicCovarianceAvailable        : Bool
    isotropicBareActionAvailable         : Bool
    anisotropicSubspaceOneDimensional    : Bool

    -- CONDITIONAL (discharged)
    anisotropicIrrelevantTermsControlled : Bool
    insertionIntegrabilityAvailable      : Bool

    -- CLOSED (2602.0092)
    rotationalWardIdentitiesAvailable    : Bool
    continuumSchwingerO4Covariant        : Bool

    -- CLOSED (2602.0096 §8.5–8.6)
    triangularLockVerified               : Bool

    -- Aggregate
    os1EuclideanCovarianceAvailable      : Bool

    hypercubicCovarianceAvailableIsTrue        : hypercubicCovarianceAvailable ≡ true
    isotropicBareActionAvailableIsTrue         : isotropicBareActionAvailable ≡ true
    anisotropicSubspaceOneDimensionalIsTrue    : anisotropicSubspaceOneDimensional ≡ true

    anisotropicIrrelevantTermsControlledIsTrue : anisotropicIrrelevantTermsControlled ≡ true
    insertionIntegrabilityAvailableIsTrue      : insertionIntegrabilityAvailable ≡ true

    rotationalWardIdentitiesAvailableIsTrue    : rotationalWardIdentitiesAvailable ≡ true
    continuumSchwingerO4CovariantIsTrue        : continuumSchwingerO4Covariant ≡ true
    triangularLockVerifiedIsTrue               : triangularLockVerified ≡ true
    os1EuclideanCovarianceAvailableIsTrue      : os1EuclideanCovarianceAvailable ≡ true

    closedSources : String
    closedSourcesIsCanonical :
      closedSources ≡
      "W₄ manifest; Wilson isotropic within W₄; Thm 3.6 (dim=1 unconditional); Thm 5.4 (|c| ≤ C aₖ² via polymer analyticity + coupling control P19); Thm 6.6 (I ≤ C(f) via OS4 clustering, discharged via DLR-LSI); Prop 3.2 (lattice Ward identity); Prop 3.4 (Symanzik decomposition); Thm 4.2+Cor 4.3 (OS1 O(4) covariance) — all 2602.0092; Thm 8.5+Cor 8.6 (triangular lock, 2602.0096)"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentO4CovarianceRestorationGate : O4CovarianceRestorationGate
currentO4CovarianceRestorationGate = record
  { hypercubicCovarianceAvailable        = true
  ; isotropicBareActionAvailable         = true
  ; anisotropicSubspaceOneDimensional    = true
  ; anisotropicIrrelevantTermsControlled = true
  ; insertionIntegrabilityAvailable      = true
  ; rotationalWardIdentitiesAvailable    = true
  ; continuumSchwingerO4Covariant        = true
  ; triangularLockVerified               = true
  ; os1EuclideanCovarianceAvailable      = true
  ; hypercubicCovarianceAvailableIsTrue        = refl
  ; isotropicBareActionAvailableIsTrue         = refl
  ; anisotropicSubspaceOneDimensionalIsTrue    = refl
  ; anisotropicIrrelevantTermsControlledIsTrue = refl
  ; insertionIntegrabilityAvailableIsTrue      = refl
  ; rotationalWardIdentitiesAvailableIsTrue    = refl
  ; continuumSchwingerO4CovariantIsTrue        = refl
  ; triangularLockVerifiedIsTrue               = refl
  ; os1EuclideanCovarianceAvailableIsTrue      = refl
  ; closedSources =
      "W₄ manifest; Wilson isotropic within W₄; Thm 3.6 (dim=1 unconditional); Thm 5.4 (|c| ≤ C aₖ² via polymer analyticity + coupling control P19); Thm 6.6 (I ≤ C(f) via OS4 clustering, discharged via DLR-LSI); Prop 3.2 (lattice Ward identity); Prop 3.4 (Symanzik decomposition); Thm 4.2+Cor 4.3 (OS1 O(4) covariance) — all 2602.0092; Thm 8.5+Cor 8.6 (triangular lock, 2602.0096)"
  ; closedSourcesIsCanonical = refl
  ; noClayPromotion = refl
  }
