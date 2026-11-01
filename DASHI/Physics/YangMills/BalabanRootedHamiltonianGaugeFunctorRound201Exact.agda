{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRootedHamiltonianGaugeFunctorRound201Exact where

------------------------------------------------------------------------
-- ROUND201 BIDI: GAUGE-ARROW FUNCTORIALITY -> ROOTED NORMALIZATION COMMUTES H.
--
-- R199 required two physical laws: H preserves the rooted slice and N H = H N.
-- R200 supplies the missing proof-relevant gauge-action groupoid operations.
-- The second R199 law is therefore not independent.
--
-- If H sends every gauge-action arrow to a gauge-action arrow between its
-- outputs, preserving basedness, then for any field U:
--
--   H(U) -> N(H(U))              normalization arrow
--   H(U) -> H(N(U))              H applied to U -> N(U)
--
-- are based arrows from the same source.  Invert the first and compose with the
-- second to obtain N(H(U)) -> H(N(U)). Both endpoints are rooted when H
-- preserves the rooted slice, so rooted uniqueness forces pointwise equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196
import DASHI.Physics.YangMills.BalabanRootedQuotientHamiltonianDescentRound199Exact as R199
import DASHI.Physics.YangMills.BalabanBasedGaugeActionGroupoidRound200Exact as R200

record RootedHamiltonianGaugeFunctorInputs
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base) : Set₁ where
  field
    hamiltonian :
      Covariance.DirectedGaugeField4 N group →
      Covariance.DirectedGaugeField4 N group

    hamiltonianPreservesRootedSlice :
      ∀ quotient →
      Rooted.RadialGaugeField group paths
        (hamiltonian (R196.representativeField quotient))

    mapGaugeActionArrow :
      ∀ {left right} →
      Free.GaugeActionArrow group left right →
      Free.GaugeActionArrow group (hamiltonian left) (hamiltonian right)

    mapBasedGaugeActionArrow :
      ∀ {left right}
        (arrow : Free.GaugeActionArrow group left right) →
      Free.BasedGaugeFunction group base (Free.gauge arrow) →
      Free.BasedGaugeFunction group base
        (Free.gauge (mapGaugeActionArrow arrow))

open RootedHamiltonianGaugeFunctorInputs public

hamiltonianNormalizationTriangle :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (inputs : RootedHamiltonianGaugeFunctorInputs group base paths)
    field →
  Free.GaugeActionArrow group
    (R196.representativeField
      (R196.normalizeToFiniteRootedGaugeQuotient group base paths
        (hamiltonian inputs field)))
    (hamiltonian inputs
      (R196.representativeField
        (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)))
hamiltonianNormalizationTriangle
    {group = group} {base = base} {paths = paths} inputs field =
  let
    rawNormalization =
      R196.normalizationGaugeArrow group base paths field

    mappedNormalization =
      mapGaugeActionArrow inputs rawNormalization

    outputNormalization =
      R196.normalizationGaugeArrow group base paths (hamiltonian inputs field)
  in
  R200.composeGaugeActionArrows
    (R200.inverseGaugeActionArrow outputNormalization)
    mappedNormalization

hamiltonianNormalizationTriangleIsBased :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (inputs : RootedHamiltonianGaugeFunctorInputs group base paths)
    field →
  Free.BasedGaugeFunction group base
    (Free.gauge (hamiltonianNormalizationTriangle inputs field))
hamiltonianNormalizationTriangleIsBased
    {group = group} {base = base} {paths = paths} inputs field =
  let
    rawNormalization =
      R196.normalizationGaugeArrow group base paths field

    rawNormalizationBased =
      R196.normalizationGaugeArrowIsBased group base paths field

    mappedNormalization =
      mapGaugeActionArrow inputs rawNormalization

    mappedNormalizationBased =
      mapBasedGaugeActionArrow inputs rawNormalization rawNormalizationBased

    outputNormalization =
      R196.normalizationGaugeArrow group base paths (hamiltonian inputs field)

    outputNormalizationBased =
      R196.normalizationGaugeArrowIsBased
        group base paths (hamiltonian inputs field)
  in
  R200.basedCompositeArrow
    (R200.inverseGaugeActionArrow outputNormalization)
    mappedNormalization
    (R200.basedInverseArrow outputNormalization outputNormalizationBased)
    mappedNormalizationBased

hamiltonianCommutesWithRootedNormalization :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (inputs : RootedHamiltonianGaugeFunctorInputs group base paths)
    field bond →
  R196.representativeField
    (R196.normalizeToFiniteRootedGaugeQuotient group base paths
      (hamiltonian inputs field)) bond
  ≡ hamiltonian inputs
      (R196.representativeField
        (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)) bond
hamiltonianCommutesWithRootedNormalization
    {group = group} {base = base} {paths = paths} inputs field bond =
  let
    left = R196.normalizeToFiniteRootedGaugeQuotient
      group base paths (hamiltonian inputs field)

    normalizedInput = R196.normalizeToFiniteRootedGaugeQuotient
      group base paths field

    rightField = hamiltonian inputs (R196.representativeField normalizedInput)

    leftRadial = R196.representativeIsRooted left
    rightRadial = hamiltonianPreservesRootedSlice inputs normalizedInput

    triangle = hamiltonianNormalizationTriangle inputs field
    triangleBased = hamiltonianNormalizationTriangleIsBased inputs field
  in
  Rooted.rootedGaugeRepresentativeUniqueInBasedOrbit
    group paths
    (R196.representativeField left)
    rightField
    leftRadial
    rightRadial
    triangle
    triangleBased
    bond

asRootedHamiltonianDescentInputs :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  RootedHamiltonianGaugeFunctorInputs group base paths →
  R199.RootedHamiltonianDescentInputs group base paths
asRootedHamiltonianDescentInputs inputs = record
  { R199.RootedHamiltonianDescentInputs.hamiltonian = hamiltonian inputs
  ; R199.RootedHamiltonianDescentInputs.hamiltonianPreservesRootedSlice =
      hamiltonianPreservesRootedSlice inputs
  ; R199.RootedHamiltonianDescentInputs.hamiltonianCommutesWithRootedNormalization =
      hamiltonianCommutesWithRootedNormalization inputs
  }

rootedHamiltonianGaugeFunctorRound201Level : ProofLevel
rootedHamiltonianGaugeFunctorRound201Level = machineChecked

rootedHamiltonianNormalizationDerivedRound201Level : ProofLevel
rootedHamiltonianNormalizationDerivedRound201Level = machineChecked

-- Strongest surviving finite Hamiltonian seam after R201: identify the actual
-- finite YM Hamiltonian as a rooted-slice-preserving endofunctor on the based
-- gauge-action groupoid.  Normalization commutation and quotient descent are
-- generated downstream.
literalFiniteYMHamiltonianGaugeArrowFunctorRound201Level : ProofLevel
literalFiniteYMHamiltonianGaugeArrowFunctorRound201Level = conditional

literalFiniteYMHamiltonianRootedSlicePreservationRound201Level : ProofLevel
literalFiniteYMHamiltonianRootedSlicePreservationRound201Level = conditional
