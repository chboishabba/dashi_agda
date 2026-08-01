module DASHI.Physics.YangMills.BalabanClayGate4GaugeTaylorLocalizationExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4DimockNormalizedPolymerReblockingExact as Reblocking

------------------------------------------------------------------------
-- Gauge-invariant Taylor localization for normalized polymer reblocking.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Field Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban, I. Small Fields",
-- Reviews in Mathematical Physics 25 (7) (2013), article 1330010.
-- arXiv:1108.1335v2. DOI: 10.1142/S0129055X13300100.
--
-- The localization operator extracts only the relevant/marginal sector allowed
-- by gauge invariance and lattice symmetries.  In four-dimensional pure gauge
-- theory the named physical sector is vacuum energy plus the F^2 coupling.
-- Gauge-fixing or constraint terms may be carried only when the selected
-- formulation proves that they are required rather than generated artifacts.
------------------------------------------------------------------------

record GaugeTaylorLocalization (Activity : Set) : Set₁ where
  field
    zero : Activity
    add : Activity → Activity → Activity
    localize remainder : Activity → Activity

    GaugeInvariant LatticeSymmetric ReflectionCompatible : Activity → Set
    RelevantGaugeSector : Activity → Set

    decomposition : ∀ activity →
      activity ≡ add (localize activity) (remainder activity)

    localizationIdempotent : ∀ activity →
      localize (localize activity) ≡ localize activity

    localizedRelevant : ∀ activity →
      GaugeInvariant activity →
      LatticeSymmetric activity →
      ReflectionCompatible activity →
      RelevantGaugeSector (localize activity)

    remainderHasNoRelevantPart : ∀ activity →
      localize (remainder activity) ≡ zero

open GaugeTaylorLocalization public

record VacuumCurvatureRelevantSector
    (Activity Coefficient : Set) : Set₁ where
  field
    zeroActivity vacuumActivity curvatureSquaredActivity : Activity
    addActivity : Activity → Activity → Activity
    scaleActivity : Coefficient → Activity → Activity

    RelevantGaugeSector : Activity → Set

    vacuumCoefficient curvatureCoefficient : Activity → Coefficient

    relevantSectorMeaning : ∀ activity →
      RelevantGaugeSector activity →
      activity
      ≡ addActivity
          (scaleActivity (vacuumCoefficient activity) vacuumActivity)
          (scaleActivity
            (curvatureCoefficient activity) curvatureSquaredActivity)

open VacuumCurvatureRelevantSector public

record GaugeNormalizedReblockingInputs
    (Activity Scalar : Set) : Set₁ where
  field
    localization : GaugeTaylorLocalization Activity
    genericReblocking : Reblocking.NormalizedPolymerReblockingData Scalar
    contraction : Reblocking.ContractiveNormalizedReblocking genericReblocking

    currentActivity reblockedActivity normalizedActivity : Activity

    RawReblockingNormMeaning : Set
    TaylorNormalizationGainMeaning : Set
    PhysicalGaugeActivityMeaning : Set

    rawReblockingNormMeaning : RawReblockingNormMeaning
    taylorNormalizationGainMeaning : TaylorNormalizationGainMeaning
    physicalGaugeActivityMeaning : PhysicalGaugeActivityMeaning

    normalizedActivityMeaning :
      normalizedActivity
      ≡ remainder localization reblockedActivity

open GaugeNormalizedReblockingInputs public

gaugeNormalizedReblockingContraction :
  ∀ {Activity Scalar}
    (inputs : GaugeNormalizedReblockingInputs Activity Scalar) →
  Reblocking.LessEqual
    (Reblocking.algebra (genericReblocking inputs))
    (Reblocking.normalizedReblockedNorm (genericReblocking inputs))
    (Reblocking.multiply
      (Reblocking.algebra (genericReblocking inputs))
      (Reblocking.targetContraction (contraction inputs))
      (Reblocking.currentNorm (genericReblocking inputs)))
gaugeNormalizedReblockingContraction inputs =
  Reblocking.normalizedReblockingBelowTargetContraction
    (contraction inputs)

gaugeTaylorProjectorAlgebraLevel : ProofLevel
gaugeTaylorProjectorAlgebraLevel = machineChecked

gaugeVacuumCurvatureRelevantSectorLevel : ProofLevel
gaugeVacuumCurvatureRelevantSectorLevel = machineChecked

gaugeNormalizedReblockingReuseLevel : ProofLevel
gaugeNormalizedReblockingReuseLevel = machineChecked

balabanGaugeTaylorExtractionSourceLevel : ProofLevel
balabanGaugeTaylorExtractionSourceLevel = standardImported

physicalGaugeRelevantSectorClassificationInputsLevel : ProofLevel
physicalGaugeRelevantSectorClassificationInputsLevel = conditional

physicalGaugeTaylorRemainderEstimateInputsLevel : ProofLevel
physicalGaugeTaylorRemainderEstimateInputsLevel = conditional
