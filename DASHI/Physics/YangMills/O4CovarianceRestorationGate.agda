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

open import Data.Nat.Base using (ℕ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_; _+ℝ_; absℝ)

postulate
  -- P20
  O6os : Set
  KerProjAniso : Set
  SpanOAniso : Set
  O6aniso : Set
  dim : Set → ℕ
  _⊕_ : Set → Set → Set
  -- P21
  c6aniso : ℕ → ℝ
  C-aniso : ℝ
  a-step : ℕ → ℝ
  -- P22
  I-insertion : ℝ → (ℝ → ℝ) → ℝ
  C-f : (ℝ → ℝ) → ℝ
  -- P28
  E-error : ℝ → ℕ → (ℝ → ℝ) → ℝ
  C-n : ℕ → ℝ
  normW11 : (ℝ → ℝ) → ℝ
  -- P29
  δsW : ℕ → ℕ → ℝ → ℝ
  g0-inv : ℝ → ℝ
  λ-coeff : ℕ → ℕ → ℝ
  Oaniso : ℝ → ℝ
  Q-O4 : ℕ → ℕ → ℝ → ℝ
  remainderSymanzik : ℝ → ℝ
  -- P30
  L-rot-operator : ℕ → ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  SchwingerLimit : ℕ → ℝ
  zeroObservable : ℕ → ℝ
  -- P32
  Z-mixing : Set → Set
  O6-aniso-W4 : Set
  O4-W4-O4inv : Set
  _⊂_ : Set → Set → Set

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0087
  ; eriksson-2602-0092
  ; eriksson-2602-0096
  ; paperImport
  ; VerificationStatus
  )

record ImportedAnisotropicSubspaceClassificationTheorem : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    subspaceDecomposition : O6os ≡ (KerProjAniso ⊕ SpanOAniso)
    dimensionIsOne : dim O6aniso ≡ 1

record ImportedAnisotropyCoeffQuadraticBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    coefficientBound : ∀ (k : ℕ) → absℝ (c6aniso k) ≤ℝ (C-aniso *ℝ (a-step k *ℝ a-step k))

record ImportedInsertionIntegrabilityBound : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    insertionBound : ∀ (η : ℝ) (f : ℝ → ℝ) → I-insertion η f ≤ℝ C-f f

record ImportedRotationalWardIdentity : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    errorBound : ∀ (η : ℝ) (n : ℕ) (f : ℝ → ℝ) → absℝ (E-error η n f) ≤ℝ (C-n n *ℝ (η *ℝ η) *ℝ normW11 f)

record ImportedSymanzikBreakingDecomposition : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    decomposition : ∀ (μ ν : ℕ) (η : ℝ) (y : ℝ) →
      δsW μ ν y ≡ (g0-inv η *ℝ g0-inv η) *ℝ (η *ℝ η) *ℝ (λ-coeff μ ν *ℝ Oaniso y +ℝ Q-O4 μ ν y +ℝ remainderSymanzik η)

record ImportedOS1EuclideanCovariance : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    covariantLimit : ∀ (μ ν : ℕ) → L-rot-operator μ ν SchwingerLimit ≡ zeroObservable

record ImportedTriangularMixingPreventiveLock : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    preventiveLock : Z-mixing O6-aniso-W4 ⊂ O4-W4-O4inv

postulate
  postulatedSubspaceDecomposition : O6os ≡ (KerProjAniso ⊕ SpanOAniso)
  postulatedDimensionIsOne : dim O6aniso ≡ 1
  postulatedCoefficientBound : ∀ (k : ℕ) → absℝ (c6aniso k) ≤ℝ (C-aniso *ℝ (a-step k *ℝ a-step k))
  postulatedInsertionBound : ∀ (η : ℝ) (f : ℝ → ℝ) → I-insertion η f ≤ℝ C-f f
  postulatedErrorBound : ∀ (η : ℝ) (n : ℕ) (f : ℝ → ℝ) → absℝ (E-error η n f) ≤ℝ (C-n n *ℝ (η *ℝ η) *ℝ normW11 f)
  postulatedDecomposition : ∀ (μ ν : ℕ) (η : ℝ) (y : ℝ) →
    δsW μ ν y ≡ (g0-inv η *ℝ g0-inv η) *ℝ (η *ℝ η) *ℝ (λ-coeff μ ν *ℝ Oaniso y +ℝ Q-O4 μ ν y +ℝ remainderSymanzik η)
  postulatedCovariantLimit : ∀ (μ ν : ℕ) → L-rot-operator μ ν SchwingerLimit ≡ zeroObservable
  postulatedPreventiveLock : Z-mixing O6-aniso-W4 ⊂ O4-W4-O4inv

anisotropicSubspaceClassificationTheoremWitness : ImportedAnisotropicSubspaceClassificationTheorem
anisotropicSubspaceClassificationTheoremWitness = record
  { sourceAuthorityId = eriksson-2602-0087
  ; theoremLocator = "Theorem 3.6"
  ; status = paperImport
  ; subspaceDecomposition = postulatedSubspaceDecomposition
  ; dimensionIsOne = postulatedDimensionIsOne
  }

anisotropyCoeffQuadraticBoundWitness : ImportedAnisotropyCoeffQuadraticBound
anisotropyCoeffQuadraticBoundWitness = record
  { sourceAuthorityId = eriksson-2602-0087
  ; theoremLocator = "Theorem 5.4"
  ; status = paperImport
  ; coefficientBound = postulatedCoefficientBound
  }

insertionIntegrabilityBoundWitness : ImportedInsertionIntegrabilityBound
insertionIntegrabilityBoundWitness = record
  { sourceAuthorityId = eriksson-2602-0087
  ; theoremLocator = "Theorem 6.6"
  ; status = paperImport
  ; insertionBound = postulatedInsertionBound
  }

importedRotationalWardIdentityWitness : ImportedRotationalWardIdentity
importedRotationalWardIdentityWitness = record
  { sourceAuthorityId = eriksson-2602-0092
  ; theoremLocator = "Proposition 3.2"
  ; status = paperImport
  ; errorBound = postulatedErrorBound
  }

importedSymanzikBreakingDecompositionWitness : ImportedSymanzikBreakingDecomposition
importedSymanzikBreakingDecompositionWitness = record
  { sourceAuthorityId = eriksson-2602-0092
  ; theoremLocator = "Proposition 3.4"
  ; status = paperImport
  ; decomposition = postulatedDecomposition
  }

importedOS1EuclideanCovarianceWitness : ImportedOS1EuclideanCovariance
importedOS1EuclideanCovarianceWitness = record
  { sourceAuthorityId = eriksson-2602-0092
  ; theoremLocator = "Theorem 4.2 + Corollary 4.3"
  ; status = paperImport
  ; covariantLimit = postulatedCovariantLimit
  }

triangularMixingPreventiveLockWitness : ImportedTriangularMixingPreventiveLock
triangularMixingPreventiveLockWitness = record
  { sourceAuthorityId = eriksson-2602-0096
  ; theoremLocator = "Theorem 8.5 + Corollary 8.6"
  ; status = paperImport
  ; preventiveLock = postulatedPreventiveLock
  }

-- ── O4CovarianceRestorationGate ─────────────────────────────────────
-- Every boolean is now true after 2602.0092 intake.

record O4CovarianceRestorationGate : Set₁ where
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

    -- Witnesses
    anisotropicSubspaceClassificationTheoremWitness : ImportedAnisotropicSubspaceClassificationTheorem
    anisotropyCoeffQuadraticBoundWitness            : ImportedAnisotropyCoeffQuadraticBound
    insertionIntegrabilityBoundWitness              : ImportedInsertionIntegrabilityBound
    importedRotationalWardIdentityWitness           : ImportedRotationalWardIdentity
    importedSymanzikBreakingDecompositionWitness    : ImportedSymanzikBreakingDecomposition
    importedOS1EuclideanCovarianceWitness           : ImportedOS1EuclideanCovariance
    triangularMixingPreventiveLockWitness           : ImportedTriangularMixingPreventiveLock

    -- Expose/Consume fields
    subspaceDecompositionField : O6os ≡ (KerProjAniso ⊕ SpanOAniso)
    dimensionIsOneField : dim O6aniso ≡ 1
    coefficientBoundField : ∀ (k : ℕ) → absℝ (c6aniso k) ≤ℝ (C-aniso *ℝ (a-step k *ℝ a-step k))
    insertionBoundField : ∀ (η : ℝ) (f : ℝ → ℝ) → I-insertion η f ≤ℝ C-f f
    errorBoundField : ∀ (η : ℝ) (n : ℕ) (f : ℝ → ℝ) → absℝ (E-error η n f) ≤ℝ (C-n n *ℝ (η *ℝ η) *ℝ normW11 f)
    decompositionField : ∀ (μ ν : ℕ) (η : ℝ) (y : ℝ) →
      δsW μ ν y ≡ (g0-inv η *ℝ g0-inv η) *ℝ (η *ℝ η) *ℝ (λ-coeff μ ν *ℝ Oaniso y +ℝ Q-O4 μ ν y +ℝ remainderSymanzik η)
    covariantLimitField : ∀ (μ ν : ℕ) → L-rot-operator μ ν SchwingerLimit ≡ zeroObservable
    preventiveLockField : Z-mixing O6-aniso-W4 ⊂ O4-W4-O4inv

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
  ; anisotropicSubspaceClassificationTheoremWitness = anisotropicSubspaceClassificationTheoremWitness
  ; anisotropyCoeffQuadraticBoundWitness            = anisotropyCoeffQuadraticBoundWitness
  ; insertionIntegrabilityBoundWitness              = insertionIntegrabilityBoundWitness
  ; importedRotationalWardIdentityWitness           = importedRotationalWardIdentityWitness
  ; importedSymanzikBreakingDecompositionWitness    = importedSymanzikBreakingDecompositionWitness
  ; importedOS1EuclideanCovarianceWitness           = importedOS1EuclideanCovarianceWitness
  ; triangularMixingPreventiveLockWitness           = triangularMixingPreventiveLockWitness
  ; subspaceDecompositionField = ImportedAnisotropicSubspaceClassificationTheorem.subspaceDecomposition anisotropicSubspaceClassificationTheoremWitness
  ; dimensionIsOneField = ImportedAnisotropicSubspaceClassificationTheorem.dimensionIsOne anisotropicSubspaceClassificationTheoremWitness
  ; coefficientBoundField = ImportedAnisotropyCoeffQuadraticBound.coefficientBound anisotropyCoeffQuadraticBoundWitness
  ; insertionBoundField = ImportedInsertionIntegrabilityBound.insertionBound insertionIntegrabilityBoundWitness
  ; errorBoundField = ImportedRotationalWardIdentity.errorBound importedRotationalWardIdentityWitness
  ; decompositionField = ImportedSymanzikBreakingDecomposition.decomposition importedSymanzikBreakingDecompositionWitness
  ; covariantLimitField = ImportedOS1EuclideanCovariance.covariantLimit importedOS1EuclideanCovarianceWitness
  ; preventiveLockField = ImportedTriangularMixingPreventiveLock.preventiveLock triangularMixingPreventiveLockWitness
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
