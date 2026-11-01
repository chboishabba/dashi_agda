module DASHI.Physics.YangMills.BalabanBlockAnchoredGaugeAverageCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- DASHI CONTRIBUTION
--
-- Consume the repository's transported-log block-average covariance theorem
-- in exactly the direction required by the selected gauge-slice problem.
-- If a fine gauge arrow restricts to the identity coarse gauge, then the
-- nonlinear block average is fixed exactly.
--
-- This module also closes the stabilizer subtlety exposed by the Round-42
-- quotient analysis.  Preservation of a fixed block average is NOT in general
-- equivalent to identity coarse restriction.  Covariance proves the exact
-- statement instead:
--
--   Q(U^g) = Q(U)
--     <=> restrict(g) stabilizes Q(U).
--
-- Hence ker(restrict) is a sufficient subgroup of the fibre-preserving gauge
-- group, while enhanced coarse stabilizers may enlarge that group.  This is
-- the configuration-space analogue of the already-proved background
-- stabilizer stratification and prevents a second false fixed-kernel shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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

CoarseGaugeStabilizesBlockAverage :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra) →
  Block → Field → CoarseGauge → Set
CoarseGaugeStabilizesBlockAverage bundle block input coarseGauge =
  Average.coarseGaugeAction bundle coarseGauge
    (Average.blockAverage bundle block input)
  ≡ Average.blockAverage bundle block input

BlockAveragePreservingGauge :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra) →
  Block → Field → Gauge → Set
BlockAveragePreservingGauge bundle block input gauge =
  Average.blockAverage bundle block (Average.gaugeAction bundle gauge input)
  ≡ Average.blockAverage bundle block input

blockAveragePreservingImpliesRestrictionStabilizes :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    block input gauge →
  BlockAveragePreservingGauge bundle block input gauge →
  CoarseGaugeStabilizesBlockAverage bundle block input
    (Average.restrictGauge bundle gauge)
blockAveragePreservingImpliesRestrictionStabilizes
    bundle block input gauge preserved =
  trans
    (sym (Average.blockAverageEquivariant bundle block gauge input))
    preserved

restrictionStabilizesImpliesBlockAveragePreserving :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    block input gauge →
  CoarseGaugeStabilizesBlockAverage bundle block input
    (Average.restrictGauge bundle gauge) →
  BlockAveragePreservingGauge bundle block input gauge
restrictionStabilizesImpliesBlockAveragePreserving
    bundle block input gauge stabilizes =
  trans
    (Average.blockAverageEquivariant bundle block gauge input)
    stabilizes

blockAveragePreservingIffRestrictionStabilizes :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    block input gauge →
  (BlockAveragePreservingGauge bundle block input gauge →
    CoarseGaugeStabilizesBlockAverage bundle block input
      (Average.restrictGauge bundle gauge))
  ×
  (CoarseGaugeStabilizesBlockAverage bundle block input
      (Average.restrictGauge bundle gauge) →
    BlockAveragePreservingGauge bundle block input gauge)
blockAveragePreservingIffRestrictionStabilizes bundle block input gauge =
  blockAveragePreservingImpliesRestrictionStabilizes bundle block input gauge ,
  restrictionStabilizesImpliesBlockAveragePreserving bundle block input gauge

coarseAnchoredRestrictionStabilizes :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set}
    (bundle : Average.CovariantBlockAverageData
      Field Gauge Block CoarseField CoarseGauge Algebra)
    (identityData : CoarseGaugeIdentityData bundle)
    block input gauge →
  CoarseAnchoredGauge bundle identityData gauge →
  CoarseGaugeStabilizesBlockAverage bundle block input
    (Average.restrictGauge bundle gauge)
coarseAnchoredRestrictionStabilizes
    bundle identityData block input gauge anchored =
  trans
    (cong
      (λ selectedCoarseGauge →
        Average.coarseGaugeAction bundle selectedCoarseGauge
          (Average.blockAverage bundle block input))
      anchored)
    (coarseIdentityActsTrivially identityData
      (Average.blockAverage bundle block input))

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
  restrictionStabilizesImpliesBlockAveragePreserving
    bundle block input gauge
    (coarseAnchoredRestrictionStabilizes
      bundle identityData block input gauge coarseAnchored)

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

blockAverageStabilizerEquivalenceLevel : ProofLevel
blockAverageStabilizerEquivalenceLevel = machineChecked

selectedCoarseAnchoredGaugeSectionStillRequiredLevel : ProofLevel
selectedCoarseAnchoredGaugeSectionStillRequiredLevel = conditional
