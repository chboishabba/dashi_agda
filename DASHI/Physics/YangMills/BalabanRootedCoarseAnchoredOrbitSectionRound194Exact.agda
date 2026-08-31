{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRootedCoarseAnchoredOrbitSectionRound194Exact where

------------------------------------------------------------------------
-- ROUND194 BIDI CROSS-POLLINATION: ONE ACTUAL CONFIGURATION-SPACE SECTION
-- SERVES BOTH THE SELECTED VARIATIONAL FIBRE AND THE FINITE GAUGE QUOTIENT.
--
-- Round42 already owns two separate ingredients:
--
--   * BasedPathGaugeSectionExact constructs an actual gauge arrow from every
--     field to a rooted representative and proves uniqueness in the based
--     rooted slice;
--   * SingleBlockRootedGaugeAverageCompatibilityExact proves that the SAME
--     rooted representative preserves Q whenever the concrete block-average
--     gauge restriction is evaluation at the selected root.
--
-- This module composes them without introducing a second quotient carrier.
-- The only remaining physical identification is the literal root-restriction
-- equality for the selected nonlinear Bałaban block average.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicLatticeGaugeCovariance as Gauge
import DASHI.Physics.YangMills.CompactLieBlockAverage as Average
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanSingleBlockRootedGaugeAverageCompatibilityExact as Compatible
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free

record RootedCoarseAnchoredOrbitSection
    {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat} {{_ : NonZero N}}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra)
    (compatibility : Compatible.RootedSingleBlockAverageData
      group paths bundle)
    (block : Block)
    (sourceField : Gauge.BondField N G) : Set₁ where
  field
    orbitLift : Rooted.BasedGaugeOrbitLift group paths sourceField

    representativePreservesBlockAverage :
      Average.blockAverage bundle block
        (Rooted.representative orbitLift)
      ≡ Average.blockAverage bundle block sourceField

open RootedCoarseAnchoredOrbitSection public

rootedCoarseAnchoredOrbitSection :
  ∀ {G Block CoarseField Algebra : Set}
    (group : Gauge.GroupStructure G)
    {N : Nat} {{_ : NonZero N}}
    (paths : Rooted.RootedPathSystem N)
    (bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra)
    (compatibility : Compatible.RootedSingleBlockAverageData
      group paths bundle)
    block sourceField →
  RootedCoarseAnchoredOrbitSection
    group paths bundle compatibility block sourceField
rootedCoarseAnchoredOrbitSection
    group paths bundle compatibility block sourceField = record
  { orbitLift = Rooted.rootedGaugeOrbitLift group paths sourceField
  ; representativePreservesBlockAverage =
      Compatible.rootedGaugeRepresentativePreservesBlockAverage
        group paths bundle compatibility block sourceField
  }

rootedCoarseAnchoredRepresentative :
  ∀ {G Block CoarseField Algebra : Set}
    {group : Gauge.GroupStructure G}
    {N : Nat} {{_ : NonZero N}}
    {paths : Rooted.RootedPathSystem N}
    {bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra}
    {compatibility : Compatible.RootedSingleBlockAverageData
      group paths bundle}
    {block : Block} {sourceField : Gauge.BondField N G} →
  RootedCoarseAnchoredOrbitSection
    group paths bundle compatibility block sourceField →
  Gauge.BondField N G
rootedCoarseAnchoredRepresentative section =
  Rooted.representative (orbitLift section)

rootedCoarseAnchoredRepresentativeInSlice :
  ∀ {G Block CoarseField Algebra : Set}
    {group : Gauge.GroupStructure G}
    {N : Nat} {{_ : NonZero N}}
    {paths : Rooted.RootedPathSystem N}
    {bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra}
    {compatibility : Compatible.RootedSingleBlockAverageData
      group paths bundle}
    {block : Block} {sourceField : Gauge.BondField N G}
    (section : RootedCoarseAnchoredOrbitSection
      group paths bundle compatibility block sourceField) →
  Rooted.RadialGaugeField group paths
    (rootedCoarseAnchoredRepresentative section)
rootedCoarseAnchoredRepresentativeInSlice section =
  Rooted.representativeInRootedSlice (orbitLift section)

rootedCoarseAnchoredRepresentativeUniqueInBasedOrbit :
  ∀ {G Block CoarseField Algebra : Set}
    {group : Gauge.GroupStructure G}
    {N : Nat} {{_ : NonZero N}}
    {paths : Rooted.RootedPathSystem N}
    {bundle : Average.CovariantBlockAverageData
      (Gauge.BondField N G)
      (Gauge.GaugeFunction N G)
      Block CoarseField G Algebra}
    {compatibility : Compatible.RootedSingleBlockAverageData
      group paths bundle}
    {block : Block} {sourceField : Gauge.BondField N G}
    (section : RootedCoarseAnchoredOrbitSection
      group paths bundle compatibility block sourceField)
    (competitor : Gauge.BondField N G) →
  Rooted.RadialGaugeField group paths competitor →
  (arrow : Free.GaugeActionArrow group
    (rootedCoarseAnchoredRepresentative section) competitor) →
  Free.BasedGaugeFunction group (Rooted.RootedPathSystem.root paths)
    (Free.gauge arrow) →
  ∀ bond → rootedCoarseAnchoredRepresentative section bond ≡ competitor bond
rootedCoarseAnchoredRepresentativeUniqueInBasedOrbit
    section competitor competitorRadial arrow based =
  Rooted.rootedGaugeRepresentativeUniqueInBasedOrbit
    _ _
    (rootedCoarseAnchoredRepresentative section)
    competitor
    (rootedCoarseAnchoredRepresentativeInSlice section)
    competitorRadial arrow based

cmp98RootedCoarseAnchoredOrbitSectionRound194Level : ProofLevel
cmp98RootedCoarseAnchoredOrbitSectionRound194Level = machineChecked

cmp98RootedCoarseAnchoredOrbitUniquenessRound194Level : ProofLevel
cmp98RootedCoarseAnchoredOrbitUniquenessRound194Level = machineChecked

-- This is now the one physical section seam shared by the two BIDI directions:
-- instantiate the selected nonlinear block-average bundle and prove its
-- `restrictGauge` is evaluation at the root used by the physical rooted path
-- system.  Everything in this owner is downstream of that equality.
literalSelectedBlockAverageRootRestrictionRound194Level : ProofLevel
literalSelectedBlockAverageRootRestrictionRound194Level = conditional
