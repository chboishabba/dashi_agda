module DASHI.Physics.YangMills.BalabanClayGate4BalabanGaugeFixingProposition5Exact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact theorem interface for Bałaban gauge-fixing Proposition 5.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Equations (1.100)--(1.109) construct the background-gauge correction as a
-- fixed point.  The proof uses beta=1/4, proves contraction factor 1/2, and
-- obtains the solution estimate
--
--   |lambda|, |D lambda|_{-1} < 8 B'_0 B_1 (alpha_0 + alpha_1).
--
-- The record below retains the source constants and hypotheses rather than
-- replacing them by a stronger, unrelated quarter-contraction target.
------------------------------------------------------------------------

record BalabanGaugeFixingProposition5
    (Configuration Correction Bound : Set) : Set₁ where
  field
    add multiply : Bound → Bound → Bound
    LessEqual StrictlyLess : Bound → Bound → Set

    zero one quarter half eight : Bound

    B0Prime B1 alpha0 alpha1 alpha4 c2 c3 : Bound

    correctionNorm derivativeNorm : Correction → Bound
    distance : Correction → Correction → Bound
    fixedPointMap : Configuration → Correction → Correction

    AdmissibleConfiguration : Configuration → Set
    InQuarterDomain : Correction → Set

    quarterDomainMeaning : ∀ correction →
      InQuarterDomain correction →
      LessEqual (correctionNorm correction)
        (multiply quarter alpha4)

    derivativeQuarterDomainMeaning : ∀ correction →
      InQuarterDomain correction →
      LessEqual (derivativeNorm correction)
        (multiply quarter alpha4)

    smallFieldHypothesis :
      StrictlyLess (add alpha0 alpha1) c2

    mapPreservesQuarterDomain : ∀ configuration correction →
      AdmissibleConfiguration configuration →
      InQuarterDomain correction →
      InQuarterDomain (fixedPointMap configuration correction)

    mapContractsByHalf : ∀ configuration left right →
      AdmissibleConfiguration configuration →
      InQuarterDomain left → InQuarterDomain right →
      LessEqual
        (distance
          (fixedPointMap configuration left)
          (fixedPointMap configuration right))
        (multiply half (distance left right))

    FixedPoint : Configuration → Correction → Set
    fixedPointMeaning : ∀ configuration correction →
      FixedPoint configuration correction →
      fixedPointMap configuration correction ≡ correction

    solution : (configuration : Configuration) →
      AdmissibleConfiguration configuration → Correction

    solutionFixed : ∀ configuration admissible →
      FixedPoint configuration (solution configuration admissible)

    solutionBound : ∀ configuration admissible →
      LessEqual
        (correctionNorm (solution configuration admissible))
        (multiply eight
          (multiply B0Prime
            (multiply B1 (add alpha0 alpha1))))

    solutionDerivativeBound : ∀ configuration admissible →
      LessEqual
        (derivativeNorm (solution configuration admissible))
        (multiply eight
          (multiply B0Prime
            (multiply B1 (add alpha0 alpha1))))

    uniquenessInC3Domain : ∀ configuration left right →
      AdmissibleConfiguration configuration →
      FixedPoint configuration left → FixedPoint configuration right →
      StrictlyLess (correctionNorm left) c3 →
      StrictlyLess (correctionNorm right) c3 →
      left ≡ right

open BalabanGaugeFixingProposition5 public

balabanGaugeFixingProposition5SourceLevel : ProofLevel
balabanGaugeFixingProposition5SourceLevel = standardImported

balabanGaugeFixingHalfContractionProfileLevel : ProofLevel
balabanGaugeFixingHalfContractionProfileLevel = standardImported

physicalGaugeFixingRepositoryIdentificationInputsLevel : ProofLevel
physicalGaugeFixingRepositoryIdentificationInputsLevel = conditional
