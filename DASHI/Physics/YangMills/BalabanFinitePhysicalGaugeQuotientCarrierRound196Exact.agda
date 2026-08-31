{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact where

------------------------------------------------------------------------
-- ROUND196 BIDI TERMINAL/SOURCE CROSS-POLLINATION
--
-- The terminal Stone/YM lane asks first for a physical gauge-quotient carrier.
-- The source-side rooted gauge machinery already gives more than a quotient
-- relation: it constructs one rooted representative in every based orbit and
-- proves uniqueness of rooted representatives inside that orbit.  Package that
-- existing theorem as an actual finite quotient carrier, then prove the
-- normalization is idempotent pointwise and retains the selected coarse block
-- average whenever Round194's literal same-object inputs are supplied.
--
-- This closes the finite SET-LEVEL quotient/representative seam only.  It does
-- not invent an inner product, Hilbert completion, strong continuity, or a
-- Stone/Yang-Mills generator identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.CompactLieBlockAverage as Average
import DASHI.Physics.YangMills.BalabanRootedCoarseAnchoredOrbitSectionRound194Exact as R194

record FiniteRootedGaugeQuotientCarrier
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base) : Set₁ where
  field
    representativeField : Covariance.DirectedGaugeField4 N group
    representativeIsRooted :
      Rooted.RadialGaugeField group paths representativeField

open FiniteRootedGaugeQuotientCarrier public

normalizeToFiniteRootedGaugeQuotient :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base) →
  Covariance.DirectedGaugeField4 N group →
  FiniteRootedGaugeQuotientCarrier group base paths
normalizeToFiniteRootedGaugeQuotient group base paths field = record
  { representativeField = Rooted.rootedGaugeRepresentative group paths field
  ; representativeIsRooted =
      Rooted.rootedGaugeRepresentativeRadial group paths field
  }

normalizationGaugeArrow :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group) →
  Free.GaugeActionArrow group field
    (representativeField
      (normalizeToFiniteRootedGaugeQuotient group base paths field))
normalizationGaugeArrow group base paths field =
  Rooted.gaugeArrow (Rooted.rootedGaugeOrbitLift group paths field)

normalizationGaugeArrowIsBased :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group) →
  Free.BasedGaugeFunction group base
    (Free.gauge (normalizationGaugeArrow group base paths field))
normalizationGaugeArrowIsBased group base paths field =
  Rooted.arrowIsBased (Rooted.rootedGaugeOrbitLift group paths field)

-- Applying the rooted normalization to an already normalized representative
-- gives the same physical bond field.  We state the exact pointwise equality,
-- avoiding any quotient axiom or proof-irrelevance assumption for record
-- equality.
finiteRootedGaugeQuotientNormalizationIdempotent :
  ∀ {N} {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group)
    bond →
  representativeField
    (normalizeToFiniteRootedGaugeQuotient group base paths
      (representativeField
        (normalizeToFiniteRootedGaugeQuotient group base paths field))) bond
  ≡ representativeField
      (normalizeToFiniteRootedGaugeQuotient group base paths field) bond
finiteRootedGaugeQuotientNormalizationIdempotent
    group base paths field bond =
  let
    first = normalizeToFiniteRootedGaugeQuotient group base paths field
    second = normalizeToFiniteRootedGaugeQuotient group base paths
      (representativeField first)
    secondLift = Rooted.rootedGaugeOrbitLift group paths
      (representativeField first)
  in
  sym
    (Rooted.rootedGaugeRepresentativeUniqueInBasedOrbit
      group paths
      (representativeField first)
      (representativeField second)
      (representativeIsRooted first)
      (representativeIsRooted second)
      (Rooted.gaugeArrow secondLift)
      (Rooted.arrowIsBased secondLift)
      bond)

-- Two normalized carrier elements in the same BASED gauge orbit are the same
-- physical bond field pointwise.  This is the finite quotient uniqueness law
-- needed before adding any Hilbert structure.
finiteRootedGaugeQuotientRepresentativeUnique :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (left right : FiniteRootedGaugeQuotientCarrier group base paths)
    (arrow : Free.GaugeActionArrow group
      (representativeField left) (representativeField right)) →
  Free.BasedGaugeFunction group base (Free.gauge arrow) →
  ∀ bond → representativeField left bond ≡ representativeField right bond
finiteRootedGaugeQuotientRepresentativeUnique
    {group = group} {paths = paths} left right arrow based =
  Rooted.rootedGaugeRepresentativeUniqueInBasedOrbit
    group paths
    (representativeField left)
    (representativeField right)
    (representativeIsRooted left)
    (representativeIsRooted right)
    arrow based

-- Same-object weld to the selected/coarse fibre.  Round194 proves that this
-- exact rooted representative preserves the nonlinear block average once the
-- physical gauge action and root restriction equalities are instantiated.
finiteRootedGaugeQuotientPreservesSelectedBlockAverage :
  ∀ {Block CoarseField Algebra N}
    {{nz : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (bundle : Average.CovariantBlockAverageData
      (Covariance.DirectedGaugeField4 N group)
      (Covariance.GaugeFunction4 N group)
      Block CoarseField (Transport.Carrier group) Algebra)
    (inputs : R194.RootedBlockAverageSameObjectInputs group base paths bundle)
    block field →
  Average.blockAverage bundle block
    (representativeField
      (normalizeToFiniteRootedGaugeQuotient group base paths field))
  ≡ Average.blockAverage bundle block field
finiteRootedGaugeQuotientPreservesSelectedBlockAverage
    group base paths bundle inputs block field =
  R194.representativePreservesBlockAverage
    (R194.rootedCoarseAnchoredOrbitSection
      group base paths bundle inputs block field)

finitePhysicalGaugeQuotientCarrierRound196Level : ProofLevel
finitePhysicalGaugeQuotientCarrierRound196Level = machineChecked

finitePhysicalGaugeQuotientIdempotenceRound196Level : ProofLevel
finitePhysicalGaugeQuotientIdempotenceRound196Level = machineChecked

finitePhysicalGaugeQuotientUniquenessRound196Level : ProofLevel
finitePhysicalGaugeQuotientUniquenessRound196Level = machineChecked

finitePhysicalGaugeQuotientSelectedFibreCompatibilityRound196Level : ProofLevel
finitePhysicalGaugeQuotientSelectedFibreCompatibilityRound196Level = machineChecked
