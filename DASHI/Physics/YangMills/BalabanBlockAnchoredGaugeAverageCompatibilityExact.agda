module DASHI.Physics.YangMills.BalabanBlockAnchoredGaugeAverageCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Consume the repository's transported-log block-average covariance theorem
-- in exactly the direction required by the selected gauge-slice problem.
-- If a fine gauge arrow restricts to the identity coarse gauge, then the
-- nonlinear block average is fixed *exactly*.
--
-- This identifies the correct slice condition after the raw-780 no-go: a
-- merely single-root based gauge does not by itself imply preservation of all
-- block averages.  What is sufficient is a block/coarse-anchored gauge whose
-- restriction is the coarse identity.  The theorem below is algebraic and
-- exact; constructing such a coarse-anchored section for the selected
-- variational fibre remains a separate geometric producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieBlockAverage as Average

record CoarseGaugeIdentityData
    {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra) : Set₁ where
  field
    coarseIdentity : CoarseGauge
    coarseIdentityActsTrivially : ∀ coarseField →
      Average.coarseGaugeAction bundle coarseIdentity coarseField
      ≡ coarseField

open CoarseGaugeIdentityData public

CoarseAnchoredGauge :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra) →
  CoarseGaugeIdentityData bundle → Gauge → Set
CoarseAnchoredGauge bundle identityData gauge =
  Average.restrictGauge bundle gauge ≡ coarseIdentity identityData

blockAverageFixedByCoarseIdentityGauge :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    (identityData : CoarseGaugeIdentityData bundle)
    block gauge input →
  CoarseAnchoredGauge bundle identityData gauge →
  Average.blockAverage bundle block (Average.gaugeAction bundle gauge input)
  ≡ Average.blockAverage bundle block input
blockAverageFixedByCoarseIdentityGauge
    bundle identityData block gauge input coarseAnchored =
  trans
    (Average.blockAverageEquivariant bundle block gauge input)
    (trans
      (cong
        (λ selectedCoarseGauge →
          Average.coarseGaugeAction bundle selectedCoarseGauge
            (Average.blockAverage bundle block input))
        coarseAnchored)
      (coarseIdentityActsTrivially identityData
        (Average.blockAverage bundle block input)))

record BlockAverageCompatibleGaugeOrbitLift
    {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    (identityData : CoarseGaugeIdentityData bundle)
    (block : Block)
    (source : Field) : Set₁ where
  field
    gauge : Gauge
    coarseAnchored : CoarseAnchoredGauge bundle identityData gauge
    representative : Field
    representativeExact :
      representative ≡ Average.gaugeAction bundle gauge source
    averagePreserved :
      Average.blockAverage bundle block representative
      ≡ Average.blockAverage bundle block source

open BlockAverageCompatibleGaugeOrbitLift public

coarseAnchoredGaugeOrbitLift :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    (identityData : CoarseGaugeIdentityData bundle)
    block source gauge →
  CoarseAnchoredGauge bundle identityData gauge →
  BlockAverageCompatibleGaugeOrbitLift
    bundle identityData block source
coarseAnchoredGaugeOrbitLift bundle identityData block source gauge anchored =
  record
    { gauge = gauge
    ; coarseAnchored = anchored
    ; representative = Average.gaugeAction bundle gauge source
    ; representativeExact = refl
    ; averagePreserved =
        blockAverageFixedByCoarseIdentityGauge
          bundle identityData block gauge source anchored
    }

blockAnchoredGaugeAverageCompatibilityLevel : ProofLevel
blockAnchoredGaugeAverageCompatibilityLevel = machineChecked

selectedCoarseAnchoredGaugeSectionStillRequiredLevel : ProofLevel
selectedCoarseAnchoredGaugeSectionStillRequiredLevel = conditional
