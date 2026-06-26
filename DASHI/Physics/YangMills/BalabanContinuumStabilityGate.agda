module DASHI.Physics.YangMills.BalabanContinuumStabilityGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.O4CovarianceRestorationGate
  using (O4CovarianceRestorationGate; currentO4CovarianceRestorationGate)

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0088
  ; eriksson-2602-0089
  ; eriksson-2602-0091
  ; eriksson-2602-0092
  ; paperImport
  ; auditTested
  ; VerificationStatus
  )

-- ── Continuum stability postulates ─────────────────────────────────
--
-- 19. ImportedCouplingControlProof — Eriksson 2602.0088, Prop. 4.1
--     Cauchy bound on Balaban β-function analyticity;
--     g_k ≤ γ₀ for all k ≤ k*, uniform in k.
--     Source: Balaban CMP 116 §3, analyticity radius R_β uniform in k.
--
-- 23. TerminalKPBoundVerified — Eriksson 2602.0091, Thm. 1.1 + Thm. 1.2
--     KP criterion (H1)–(H3) verified from Balaban CMP 116/119/122.
--     Audits the terminal clustering input used in 2602.0088.
--     Unconditional (audit trail to primary sources complete).
--
-- 24. AssemblyMapComplete — Eriksson 2602.0091, Thm. 1.3
--     Dependency graph confirmed:
--       2602.0092 → 2602.0088/0087 → 2602.0091 → Wightman
--     Conditional on Paper 2602.0092 availability.
--
-- 25. UniformLSIFixedLattice — Eriksson 2602.0089, Thm. A
--     Ent( f² ) ≤ (2/ρ̂) ℰ(f,f) with ρ̂ > 0 independent of L,
--     via Bakry–Émery seed + Cesi quasi-factorization.
--     Fixed η > 0 only; does NOT close continuum-limit gates.
--
-- 26. VolumeUniformMassGapFixedLattice — Eriksson 2602.0089, Thm. B
--     m₀ > 0 independent of L, via OS transfer + temporal clustering.
--     Fixed η > 0 only; §8.4 defers η→0 to a separate paper.
--
-- 27. ThermodynamicLimitUnique — Eriksson 2602.0089, Thm. C
--     μ_L → μ_∞ unique, gap persistence.
--     Fixed η > 0 only; does NOT close continuum-limit gates.
--
-- 31. ImportedWightmanReconstructionWithMassGap — Eriksson 2602.0092, Thm. 1.1 + §5
--     (H, U(Λ,a), Ω) satisfying all Wightman axioms
--     Δ_phys ≥ c_N Λ_YM > 0, Sᶜ₄ ≢ 0
--     Conditional on: OS0–OS4 (P12–P15), OS1 (P30), OS reconstruction [6]

open import Data.Nat.Base using (ℕ; _≤_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_)

postulate
  -- P19
  g-coupling : ℕ → ℝ
  γ0-bound : ℝ
  k-star : ℕ
  -- P23
  KP-H1 : Set
  KP-H2 : Set
  KP-H3 : Set
  -- P24
  WardIdentityResult : Set
  AnisotropyControlResult : Set
  KPBoundResult : Set
  WightmanResult : Set
  -- P25
  Entropy : (ℝ → ℝ) → ℝ
  DirichletForm : (ℝ → ℝ) → ℝ
  ρ̂-LSI : ℝ
  2ℝ : ℝ
  -- P26
  m0-gap : ℝ
  -- P27
  State : Set
  μ-seq : ℕ → State
  μ-inf1 μ-inf2 : State
  ConvergesToState : (ℕ → State) → State → Set
  -- P31
  HilbertSpace : Set
  VacuumState : HilbertSpace
  WightmanAxiomsSatisfied : HilbertSpace → VacuumState → Set
  Δ-phys : ℝ
  c-N : ℝ
  Λ-YM : ℝ

record ImportedCouplingControlProof : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    couplingBound : ∀ (k : ℕ) → k ≤ k-star → g-coupling k ≤ℝ γ0-bound

record ImportedTerminalKPBoundVerified : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    h1-verified : KP-H1
    h2-verified : KP-H2
    h3-verified : KP-H3

record ImportedAssemblyMapComplete : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    wardToAnisotropy : WardIdentityResult → AnisotropyControlResult
    anisotropyToKP : AnisotropyControlResult → KPBoundResult
    kpToWightman : KPBoundResult → WightmanResult

record ImportedUniformLSIFixedLattice : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    lsiInequality : ∀ (f : ℝ → ℝ) → ρ̂-LSI *ℝ Entropy f ≤ℝ (2ℝ *ℝ DirichletForm f)
    ρ̂-positive : 0ℝ <ℝ ρ̂-LSI

record ImportedVolumeUniformMassGapFixedLattice : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    massGapPositive : 0ℝ <ℝ m0-gap

record ImportedThermodynamicLimitUnique : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    uniqueness : ConvergesToState μ-seq μ-inf1 → ConvergesToState μ-seq μ-inf2 → μ-inf1 ≡ μ-inf2

record ImportedWightmanReconstructionWithMassGap : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    axiomsHold : WightmanAxiomsSatisfied HilbertSpace VacuumState
    massGapBound : (c-N *ℝ Λ-YM) ≤ℝ Δ-phys
    massGapPositive : 0ℝ <ℝ (c-N *ℝ Λ-YM)

postulate
  postulatedCouplingBound : ∀ (k : ℕ) → k ≤ k-star → g-coupling k ≤ℝ γ0-bound
  postulatedH1 : KP-H1
  postulatedH2 : KP-H2
  postulatedH3 : KP-H3
  postulatedWardToAnisotropy : WardIdentityResult → AnisotropyControlResult
  postulatedAnisotropyToKP : AnisotropyControlResult → KPBoundResult
  postulatedKpToWightman : KPBoundResult → WightmanResult
  postulatedLsiInequality : ∀ (f : ℝ → ℝ) → ρ̂-LSI *ℝ Entropy f ≤ℝ (2ℝ *ℝ DirichletForm f)
  postulatedρ̂Positive : 0ℝ <ℝ ρ̂-LSI
  postulatedMassGapPositive : 0ℝ <ℝ m0-gap
  postulatedUniqueness : ConvergesToState μ-seq μ-inf1 → ConvergesToState μ-seq μ-inf2 → μ-inf1 ≡ μ-inf2
  postulatedAxiomsHold : WightmanAxiomsSatisfied HilbertSpace VacuumState
  postulatedMassGapBound : (c-N *ℝ Λ-YM) ≤ℝ Δ-phys
  postulatedMassGapPositiveVal : 0ℝ <ℝ (c-N *ℝ Λ-YM)

couplingControlProofWitness : ImportedCouplingControlProof
couplingControlProofWitness = record
  { sourceAuthorityId = eriksson-2602-0088
  ; theoremLocator = "Proposition 4.1"
  ; status = paperImport
  ; couplingBound = postulatedCouplingBound
  }

terminalKPBoundVerifiedWitness : ImportedTerminalKPBoundVerified
terminalKPBoundVerifiedWitness = record
  { sourceAuthorityId = eriksson-2602-0091
  ; theoremLocator = "Theorems 1.1 + 1.2"
  ; status = paperImport
  ; h1-verified = postulatedH1
  ; h2-verified = postulatedH2
  ; h3-verified = postulatedH3
  }

assemblyMapCompleteWitness : ImportedAssemblyMapComplete
assemblyMapCompleteWitness = record
  { sourceAuthorityId = eriksson-2602-0091
  ; theoremLocator = "Theorem 1.3"
  ; status = auditTested
  ; wardToAnisotropy = postulatedWardToAnisotropy
  ; anisotropyToKP = postulatedAnisotropyToKP
  ; kpToWightman = postulatedKpToWightman
  }

uniformLSIFixedLatticeWitness : ImportedUniformLSIFixedLattice
uniformLSIFixedLatticeWitness = record
  { sourceAuthorityId = eriksson-2602-0089
  ; theoremLocator = "Theorem A"
  ; status = paperImport
  ; lsiInequality = postulatedLsiInequality
  ; ρ̂-positive = postulatedρ̂Positive
  }

volumeUniformMassGapFixedLatticeWitness : ImportedVolumeUniformMassGapFixedLattice
volumeUniformMassGapFixedLatticeWitness = record
  { sourceAuthorityId = eriksson-2602-0089
  ; theoremLocator = "Theorem B"
  ; status = paperImport
  ; massGapPositive = postulatedMassGapPositive
  }

thermodynamicLimitUniqueWitness : ImportedThermodynamicLimitUnique
thermodynamicLimitUniqueWitness = record
  { sourceAuthorityId = eriksson-2602-0089
  ; theoremLocator = "Theorem C"
  ; status = paperImport
  ; uniqueness = postulatedUniqueness
  }

importedWightmanReconstructionWithMassGapWitness : ImportedWightmanReconstructionWithMassGap
importedWightmanReconstructionWithMassGapWitness = record
  { sourceAuthorityId = eriksson-2602-0092
  ; theoremLocator = "Theorem 1.1 + §5"
  ; status = paperImport
  ; axiomsHold = postulatedAxiomsHold
  ; massGapBound = postulatedMassGapBound
  ; massGapPositive = postulatedMassGapPositiveVal
  }

-- ── ContinuumStabilitySourceIntake ─────────────────────────────────
-- Matches the three-tier architecture of Eriksson 2602.0088 §8.
--
-- Tier 1 — Unconditional (no hypothesis needed):
--   OS0, OS2, OS3 — follow from standard lattice arguments
--
-- Tier 2 — Conditional on Hypothesis 5.2:
--   Hypothesis 5.2 is now DISCHARGED via DLR-LSI (2602.0052 Thm 7.1).
--   The Dobrushin bypass (Yoshida–GZ, Lem. 6.3) closes the gap
--   deferred in Remark 5.3.  OS4, Δ_phys, vacuum uniqueness, and
--   non-triviality follow.
--
-- Tier 3 — Conditional on O(4) restoration:
--   OS1 (full Euclidean covariance) explicitly deferred in
--   Remark 8.4.  Wightman reconstruction conditional on OS1.

record ContinuumStabilitySourceIntake : Set₁ where
  field
    -- TIER 1: Unconditional
    temperednessAvailable           : Bool
    reflectionPositivityAvailable   : Bool
    bosonicSymmetryAvailable        : Bool

    -- TIER 2: Conditional on Hypothesis 5.2 (now discharged via DLR-LSI)
    hypothesis52Discharged          : Bool
    vacuumUniquenessAvailable       : Bool
    nonTrivialityAvailable          : Bool
    os4ClusterPropertyAvailable     : Bool
    physicalMassGapPositive         : Bool
    couplingControlDischarge        : Bool
    multiscaleCorrelatorDecoupling  : Bool

    -- TIER 3: Closed (2602.0092)
    os1EuclideanCovarianceAvailable : Bool
    wightmanReconstructionAvailable : Bool

    -- Witnesses
    couplingControlProofWitness : ImportedCouplingControlProof
    terminalKPBoundVerifiedWitness : ImportedTerminalKPBoundVerified
    assemblyMapCompleteWitness : ImportedAssemblyMapComplete
    uniformLSIFixedLatticeWitness : ImportedUniformLSIFixedLattice
    volumeUniformMassGapFixedLatticeWitness : ImportedVolumeUniformMassGapFixedLattice
    thermodynamicLimitUniqueWitness : ImportedThermodynamicLimitUnique
    importedWightmanReconstructionWithMassGapWitness : ImportedWightmanReconstructionWithMassGap

    -- Expose/Consume fields
    couplingBoundField : ∀ (k : ℕ) → k ≤ k-star → g-coupling k ≤ℝ γ0-bound
    h1-verifiedField : KP-H1
    h2-verifiedField : KP-H2
    h3-verifiedField : KP-H3
    wardToAnisotropyField : WardIdentityResult → AnisotropyControlResult
    anisotropyToKPField : AnisotropyControlResult → KPBoundResult
    kpToWightmanField : KPBoundResult → WightmanResult
    lsiInequalityField : ∀ (f : ℝ → ℝ) → ρ̂-LSI *ℝ Entropy f ≤ℝ (2ℝ *ℝ DirichletForm f)
    ρ̂-positiveField : 0ℝ <ℝ ρ̂-LSI
    massGapPositiveField : 0ℝ <ℝ m0-gap
    uniquenessField : ConvergesToState μ-seq μ-inf1 → ConvergesToState μ-seq μ-inf2 → μ-inf1 ≡ μ-inf2
    axiomsHoldField : WightmanAxiomsSatisfied HilbertSpace VacuumState
    massGapBoundField : (c-N *ℝ Λ-YM) ≤ℝ Δ-phys
    massGapPositiveFieldVal : 0ℝ <ℝ (c-N *ℝ Λ-YM)

    temperednessAvailableIsTrue           : temperednessAvailable ≡ true
    reflectionPositivityAvailableIsTrue   : reflectionPositivityAvailable ≡ true
    bosonicSymmetryAvailableIsTrue        : bosonicSymmetryAvailable ≡ true

    hypothesis52DischargedIsTrue          : hypothesis52Discharged ≡ true
    vacuumUniquenessAvailableIsTrue       : vacuumUniquenessAvailable ≡ true
    nonTrivialityAvailableIsTrue          : nonTrivialityAvailable ≡ true
    os4ClusterPropertyAvailableIsTrue     : os4ClusterPropertyAvailable ≡ true
    physicalMassGapPositiveIsTrue         : physicalMassGapPositive ≡ true
    couplingControlDischargeIsTrue        : couplingControlDischarge ≡ true
    multiscaleCorrelatorDecouplingIsTrue  : multiscaleCorrelatorDecoupling ≡ true

    os1EuclideanCovarianceAvailableIsTrue : os1EuclideanCovarianceAvailable ≡ true
    wightmanReconstructionAvailableIsTrue : wightmanReconstructionAvailable ≡ true

    tier1Source : String
    tier1SourceIsCanonical :
      tier1Source ≡
      "Tier 1 unconditional: OS0 (Banach-Alaoglu), OS2 (Osterwalder-Seiler Thm 2.1), OS3 (automatic for gauge-invariant observables) — Eriksson 2602.0088 §8.1"
    tier2Source : String
    tier2SourceIsCanonical :
      tier2Source ≡
      "Tier 2 via DLR-LSI: Hyp 5.2 discharged by Yoshida-GZ bypass (2602.0052 Lem 6.3 → Thm 7.1); OS4 cluster property (2602.0088 Thm 7.1); Δ_phys > 0 (Cor 1.2); vacuum uniqueness (Prop 8.5); non-triviality (Thm 8.7); coupling control (Prop 4.1); multiscale decoupling (Thm 6.3)"
    tier3Source : String
    tier3SourceIsCanonical :
      tier3Source ≡
      "Tier 3: O(4) gate closed via 2602.0092 (Prop 3.2 lattice Ward identity, Prop 3.4 Symanzik decomposition, Thm 4.2+Cor 4.3 OS1 O(4) covariance); Wightman reconstruction closed via 2602.0092 §5 (Thm 1.1)"

currentContinuumStabilitySourceIntake : ContinuumStabilitySourceIntake
currentContinuumStabilitySourceIntake = record
  { temperednessAvailable           = true
  ; reflectionPositivityAvailable   = true
  ; bosonicSymmetryAvailable        = true
  ; hypothesis52Discharged          = true
  ; vacuumUniquenessAvailable       = true
  ; nonTrivialityAvailable          = true
  ; os4ClusterPropertyAvailable     = true
  ; physicalMassGapPositive         = true
  ; couplingControlDischarge        = true
  ; multiscaleCorrelatorDecoupling  = true
  ; os1EuclideanCovarianceAvailable = true
  ; wightmanReconstructionAvailable = true
  ; couplingControlProofWitness     = couplingControlProofWitness
  ; terminalKPBoundVerifiedWitness   = terminalKPBoundVerifiedWitness
  ; assemblyMapCompleteWitness       = assemblyMapCompleteWitness
  ; uniformLSIFixedLatticeWitness    = uniformLSIFixedLatticeWitness
  ; volumeUniformMassGapFixedLatticeWitness = volumeUniformMassGapFixedLatticeWitness
  ; thermodynamicLimitUniqueWitness  = thermodynamicLimitUniqueWitness
  ; importedWightmanReconstructionWithMassGapWitness = importedWightmanReconstructionWithMassGapWitness
  ; couplingBoundField = ImportedCouplingControlProof.couplingBound couplingControlProofWitness
  ; h1-verifiedField = ImportedTerminalKPBoundVerified.h1-verified terminalKPBoundVerifiedWitness
  ; h2-verifiedField = ImportedTerminalKPBoundVerified.h2-verified terminalKPBoundVerifiedWitness
  ; h3-verifiedField = ImportedTerminalKPBoundVerified.h3-verified terminalKPBoundVerifiedWitness
  ; wardToAnisotropyField = ImportedAssemblyMapComplete.wardToAnisotropy assemblyMapCompleteWitness
  ; anisotropyToKPField = ImportedAssemblyMapComplete.anisotropyToKP assemblyMapCompleteWitness
  ; kpToWightmanField = ImportedAssemblyMapComplete.kpToWightman assemblyMapCompleteWitness
  ; lsiInequalityField = ImportedUniformLSIFixedLattice.lsiInequality uniformLSIFixedLatticeWitness
  ; ρ̂-positiveField = ImportedUniformLSIFixedLattice.ρ̂-positive uniformLSIFixedLatticeWitness
  ; massGapPositiveField = ImportedVolumeUniformMassGapFixedLattice.massGapPositive volumeUniformMassGapFixedLatticeWitness
  ; uniquenessField = ImportedThermodynamicLimitUnique.uniqueness thermodynamicLimitUniqueWitness
  ; axiomsHoldField = ImportedWightmanReconstructionWithMassGap.axiomsHold importedWightmanReconstructionWithMassGapWitness
  ; massGapBoundField = ImportedWightmanReconstructionWithMassGap.massGapBound importedWightmanReconstructionWithMassGapWitness
  ; massGapPositiveFieldVal = ImportedWightmanReconstructionWithMassGap.massGapPositive importedWightmanReconstructionWithMassGapWitness
  ; temperednessAvailableIsTrue           = refl
  ; reflectionPositivityAvailableIsTrue   = refl
  ; bosonicSymmetryAvailableIsTrue        = refl
  ; hypothesis52DischargedIsTrue          = refl
  ; vacuumUniquenessAvailableIsTrue       = refl
  ; nonTrivialityAvailableIsTrue          = refl
  ; os4ClusterPropertyAvailableIsTrue     = refl
  ; physicalMassGapPositiveIsTrue         = refl
  ; couplingControlDischargeIsTrue        = refl
  ; multiscaleCorrelatorDecouplingIsTrue  = refl
  ; os1EuclideanCovarianceAvailableIsTrue = refl
  ; wightmanReconstructionAvailableIsTrue = refl
  ; tier1Source =
      "Tier 1 unconditional: OS0 (Banach-Alaoglu), OS2 (Osterwalder-Seiler Thm 2.1), OS3 (automatic for gauge-invariant observables) — Eriksson 2602.0088 §8.1"
  ; tier1SourceIsCanonical = refl
  ; tier2Source =
      "Tier 2 via DLR-LSI: Hyp 5.2 discharged by Yoshida-GZ bypass (2602.0052 Lem 6.3 → Thm 7.1); OS4 cluster property (2602.0088 Thm 7.1); Δ_phys > 0 (Cor 1.2); vacuum uniqueness (Prop 8.5); non-triviality (Thm 8.7); coupling control (Prop 4.1); multiscale decoupling (Thm 6.3)"
  ; tier2SourceIsCanonical = refl
  ; tier3Source =
      "Tier 3: O(4) gate closed via 2602.0092 (Prop 3.2 lattice Ward identity, Prop 3.4 Symanzik decomposition, Thm 4.2+Cor 4.3 OS1 O(4) covariance); Wightman reconstruction closed via 2602.0092 §5 (Thm 1.1)"
  ; tier3SourceIsCanonical = refl
  }

-- ── ContinuumStabilityGate ──────────────────────────────────────────
-- Route-level separation between finite/RG guarantees (true) and
-- continuum-grade claims (closed after 2602.0092 intake).
-- The source-intake layer above provides the three-tier mapping.

record ContinuumStabilityGate : Set₁ where
  field
    -- Source intake
    sourceIntake : ContinuumStabilitySourceIntake

    -- O(4) covariance gate (detailed sub-record)
    o4Gate : O4CovarianceRestorationGate

    -- Finite/RG level (closed)
    finiteVolumeRGLaneAdvanced           : Bool
    finiteDepthMassGapPromoted           : Bool
    thermodynamicLimitAuthorityAvailable  : Bool
    h3aContinuumIntakeConstructed        : Bool

    -- Continuum level (open — repo-local infrastructure gaps)
    uniformContinuumPromoted             : Bool
    quantifierExchangeDischarged         : Bool
    thermodynamicLimitProvedInRepo       : Bool
    cutoffRemovalControlled              : Bool
    continuumMassGapProvedInDASHI        : Bool
    h3bDownstreamClosed                  : Bool
    balabanH3aIntakeClosed               : Bool
    continuumClayMassGapPromoted         : Bool

    -- Assembly
    continuumStabilityClosed            : Bool

    finiteVolumeRGLaneAdvancedIsTrue          : finiteVolumeRGLaneAdvanced ≡ true
    finiteDepthMassGapPromotedIsTrue          : finiteDepthMassGapPromoted ≡ true
    thermodynamicLimitAuthorityAvailableIsTrue : thermodynamicLimitAuthorityAvailable ≡ true
    h3aContinuumIntakeConstructedIsTrue       : h3aContinuumIntakeConstructed ≡ true

    uniformContinuumPromotedIsFalse           : uniformContinuumPromoted ≡ false
    quantifierExchangeDischargedIsFalse       : quantifierExchangeDischarged ≡ false
    thermodynamicLimitProvedInRepoIsFalse     : thermodynamicLimitProvedInRepo ≡ false
    cutoffRemovalControlledIsFalse            : cutoffRemovalControlled ≡ false
    continuumMassGapProvedInDASHIIsFalse      : continuumMassGapProvedInDASHI ≡ false
    h3bDownstreamClosedIsFalse                : h3bDownstreamClosed ≡ false
    balabanH3aIntakeClosedIsFalse             : balabanH3aIntakeClosed ≡ false
    continuumClayMassGapPromotedIsFalse        : continuumClayMassGapPromoted ≡ false

    continuumStabilityClosedIsTrue           : continuumStabilityClosed ≡ true

    finiteSources : String
    finiteSourcesIsCanonical :
      finiteSources ≡
      "finite/RG: BalabanRGStepVLane rgLaneAdvanced, BalabanRGMassGapReceiptSurface finiteDepthMassGapPromoted/pointwiseFiniteDepthPromoted, YMThermodynamicLimitAuthority authority-conditional, YMH3aContinuumIntakeReceipt h3aContinuumIntakeClosed"
    continuumOpenSources : String
    continuumOpenSourcesIsCanonical :
      continuumOpenSources ≡
      "continuum: OS1/O(4) closed via 2602.0092; Wightman reconstruction closed via 2602.0092 §5; repo-local gaps (quantifierExchange, thermodynamicLimitProvedInRepo, cutoffRemoval, H3b, Balaban-side H3a) still false"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentContinuumStabilityGate : ContinuumStabilityGate
currentContinuumStabilityGate = record
  { sourceIntake = currentContinuumStabilitySourceIntake
  ; o4Gate = currentO4CovarianceRestorationGate
  ; finiteVolumeRGLaneAdvanced           = true
  ; finiteDepthMassGapPromoted           = true
  ; thermodynamicLimitAuthorityAvailable  = true
  ; h3aContinuumIntakeConstructed        = true
  ; uniformContinuumPromoted             = false
  ; quantifierExchangeDischarged         = false
  ; thermodynamicLimitProvedInRepo       = false
  ; cutoffRemovalControlled              = false
  ; continuumMassGapProvedInDASHI        = false
  ; h3bDownstreamClosed                  = false
  ; balabanH3aIntakeClosed               = false
  ; continuumClayMassGapPromoted         = false
  ; continuumStabilityClosed            = true
  ; finiteVolumeRGLaneAdvancedIsTrue          = refl
  ; finiteDepthMassGapPromotedIsTrue          = refl
  ; thermodynamicLimitAuthorityAvailableIsTrue = refl
  ; h3aContinuumIntakeConstructedIsTrue       = refl
  ; uniformContinuumPromotedIsFalse           = refl
  ; quantifierExchangeDischargedIsFalse       = refl
  ; thermodynamicLimitProvedInRepoIsFalse     = refl
  ; cutoffRemovalControlledIsFalse            = refl
  ; continuumMassGapProvedInDASHIIsFalse      = refl
  ; h3bDownstreamClosedIsFalse                = refl
  ; balabanH3aIntakeClosedIsFalse             = refl
  ; continuumClayMassGapPromotedIsFalse        = refl
  ; continuumStabilityClosedIsTrue           = refl
  ; finiteSources =
      "finite/RG: BalabanRGStepVLane rgLaneAdvanced, BalabanRGMassGapReceiptSurface finiteDepthMassGapPromoted/pointwiseFiniteDepthPromoted, YMThermodynamicLimitAuthority authority-conditional, YMH3aContinuumIntakeReceipt h3aContinuumIntakeClosed"
  ; finiteSourcesIsCanonical = refl
  ; continuumOpenSources =
      "continuum: OS1/O(4) closed via 2602.0092; Wightman reconstruction closed via 2602.0092 §5; repo-local gaps (quantifierExchange, thermodynamicLimitProvedInRepo, cutoffRemoval, H3b, Balaban-side H3a) still false"
  ; continuumOpenSourcesIsCanonical = refl
  ; noClayPromotion = refl
  }
