{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRootedCoarseAnchoredOrbitSectionRound194Exact where

------------------------------------------------------------------------
-- ROUND194 BIDI CROSS-POLLINATION: ONE ACTUAL CONFIGURATION-SPACE SECTION
-- SERVES BOTH THE SELECTED VARIATIONAL FIBRE AND THE FINITE GAUGE QUOTIENT.
--
-- `BalabanBasedPathGaugeSectionExact` already constructs a genuine gauge arrow
-- from every finite field to a rooted representative and proves uniqueness in
-- the based rooted slice.  `BalabanBlockAnchoredGaugeAverageCompatibilityExact`
-- already proves that a coarse-anchored gauge preserves the nonlinear block
-- average.
--
-- The two developments used different interfaces.  This owner identifies only
-- the two same-object seams needed to compose them:
--
--   1. the block-average bundle gauge action is the literal physical bond gauge
--      transformation used by the rooted section;
--   2. the bundle's fine->coarse gauge restriction is evaluation at the chosen
--      root.
--
-- Everything else -- orbit arrow, basedness, rooted-slice membership,
-- block-average preservation, and uniqueness in the based orbit -- is derived.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.CompactLieBlockAverage as Average
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanBlockAnchoredGaugeAverageCompatibilityExact as Anchored
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free

record RootedBlockAverageSameObjectInputs
    {Block CoarseField Algebra : Set}
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra) : Set₁ where
  field
    gaugeActionIsPhysical : ∀ gauge field →
      Average.gaugeAction bundle gauge field
      ≡ Covariance.gaugeTransformBond group gauge field

    restrictGaugeIsRootEvaluation : ∀ gauge →
      Average.restrictGauge bundle gauge ≡ gauge base

    coarseUnitActsTrivially : ∀ coarseField →
      Average.coarseGaugeAction bundle (Transport.unit group) coarseField
      ≡ coarseField

open RootedBlockAverageSameObjectInputs public

rootedCoarseIdentityData :
  ∀ {Block CoarseField Algebra N}
    {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra) →
  RootedBlockAverageSameObjectInputs group base paths bundle →
  Anchored.CoarseGaugeIdentityData bundle
rootedCoarseIdentityData group base paths bundle inputs = record
  { Anchored.CoarseGaugeIdentityData.coarseIdentity = Transport.unit group
  ; Anchored.CoarseGaugeIdentityData.coarseIdentityActsTrivially =
      coarseUnitActsTrivially inputs
  }

rootedGaugeFunctionIsCoarseAnchored :
  ∀ {Block CoarseField Algebra N}
    {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra)
    (inputs : RootedBlockAverageSameObjectInputs group base paths bundle)
    field →
  Anchored.CoarseAnchoredGauge bundle
    (rootedCoarseIdentityData group base paths bundle inputs)
    (Rooted.rootedGaugeFunction group paths field)
rootedGaugeFunctionIsCoarseAnchored
    group base paths bundle inputs field =
  trans
    (restrictGaugeIsRootEvaluation inputs
      (Rooted.rootedGaugeFunction group paths field))
    (Rooted.rootedGaugeFunctionBased group paths field)

record RootedCoarseAnchoredOrbitSection
    {Block CoarseField Algebra : Set}
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra)
    (inputs : RootedBlockAverageSameObjectInputs group base paths bundle)
    (block : Block)
    (sourceField : Covariance.DirectedGaugeField4 N group) : Set₁ where
  field
    orbitLift : Rooted.BasedGaugeOrbitLift group paths sourceField

    representativePreservesBlockAverage :
      Average.blockAverage bundle block
        (Rooted.representative orbitLift)
      ≡ Average.blockAverage bundle block sourceField

open RootedCoarseAnchoredOrbitSection public

rootedCoarseAnchoredOrbitSection :
  ∀ {Block CoarseField Algebra N}
    {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra)
    (inputs : RootedBlockAverageSameObjectInputs group base paths bundle)
    block sourceField →
  RootedCoarseAnchoredOrbitSection
    group base paths bundle inputs block sourceField
rootedCoarseAnchoredOrbitSection
    group base paths bundle inputs block sourceField =
  let
    gauge = Rooted.rootedGaugeFunction group paths sourceField
    identityData = rootedCoarseIdentityData group base paths bundle inputs
    anchored = rootedGaugeFunctionIsCoarseAnchored
      group base paths bundle inputs sourceField

    bundlePreserves :
      Average.blockAverage bundle block
        (Average.gaugeAction bundle gauge sourceField)
      ≡ Average.blockAverage bundle block sourceField
    bundlePreserves =
      Anchored.blockAverageFixedByCoarseIdentityGauge
        bundle identityData block gauge sourceField anchored

    physicalIsBundleAction :
      Covariance.gaugeTransformBond group gauge sourceField
      ≡ Average.gaugeAction bundle gauge sourceField
    physicalIsBundleAction =
      sym (gaugeActionIsPhysical inputs gauge sourceField)
  in
  record
    { orbitLift = Rooted.rootedGaugeOrbitLift group paths sourceField
    ; representativePreservesBlockAverage =
        trans
          (cong (Average.blockAverage bundle block) physicalIsBundleAction)
          bundlePreserves
    }

rootedCoarseAnchoredRepresentativeUniqueInBasedOrbit :
  ∀ {Block CoarseField Algebra N}
    {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra}
    {inputs : RootedBlockAverageSameObjectInputs group base paths bundle}
    {block : Block}
    {sourceField : Covariance.DirectedGaugeField4 N group}
    (section : RootedCoarseAnchoredOrbitSection
      group base paths bundle inputs block sourceField)
    (competitor : Covariance.DirectedGaugeField4 N group) →
  Rooted.RadialGaugeField group paths competitor →
  (arrow : Free.GaugeActionArrow group
    (Rooted.representative (orbitLift section)) competitor) →
  Free.BasedGaugeFunction group base (Free.gauge arrow) →
  ∀ bond → Rooted.representative (orbitLift section) bond ≡ competitor bond
rootedCoarseAnchoredRepresentativeUniqueInBasedOrbit
    {group = group} {paths = paths}
    section competitor competitorRadial arrow based =
  Rooted.rootedGaugeRepresentativeUniqueInBasedOrbit
    group paths
    (Rooted.representative (orbitLift section))
    competitor
    (Rooted.representativeInRootedSlice (orbitLift section))
    competitorRadial arrow based

cmp98RootedCoarseAnchoredOrbitSectionRound194Level : ProofLevel
cmp98RootedCoarseAnchoredOrbitSectionRound194Level = machineChecked

cmp98RootedCoarseAnchoredOrbitUniquenessRound194Level : ProofLevel
cmp98RootedCoarseAnchoredOrbitUniquenessRound194Level = machineChecked

-- Shared physical seam for both BIDI directions.  No quotient construction or
-- variational theorem is hidden here: instantiate these two equalities for the
-- literal selected nonlinear block-average implementation.
literalSelectedBlockAverageGaugeActionSameObjectRound194Level : ProofLevel
literalSelectedBlockAverageGaugeActionSameObjectRound194Level = conditional

literalSelectedBlockAverageRootRestrictionRound194Level : ProofLevel
literalSelectedBlockAverageRootRestrictionRound194Level = conditional
