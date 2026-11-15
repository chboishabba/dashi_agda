module DASHI.Physics.Plasma.Phase243CoilPlasmaFreeBoundaryMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Phase243Core54ParetoCoilExact as ParetoCoil
import DASHI.Physics.Plasma.ToroidalConstantMagnitudeHybridABCExact as ABC
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce
import DASHI.Physics.Plasma.TrappedParticleInvariantReferenceExact as Reference

------------------------------------------------------------------------
-- SAME-OBJECT COIL + PLASMA FREE-BOUNDARY FRONTIER
--
-- A winding-surface/current-potential inverse pays only an external-field
-- construction problem.  The next physical object is one finite-beta plasma
-- equilibrium in the field produced by both external currents and the plasma:
--
--   B_total = B_coil + B_plasma.
--
-- The declared ABC flow / anisotropy / route-C allocation must be solved on
-- that same state.  Only the produced B_total can then enter zero-bounce,
-- trapped-particle, FOW and energetic-particle consumers.
------------------------------------------------------------------------

record SameObjectCoilPlasmaEquilibrium
    (PhysicalState CoilField PlasmaField TotalField : Set)
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor same-object-coil-plasma-equilibrium
  field
    state : PhysicalState
    coilField : CoilField
    plasmaField : PlasmaField
    totalField : TotalField

    totalFieldIsCoilPlusPlasmaReceipt : Set
    coilFieldProducedBySelectedCurrentsReceipt : Set
    plasmaFieldProducedBySameStateCurrentReceipt : Set
    sameGeometryBoundaryReceipt : Set
    sameNormalizationReceipt : Set

    finiteBetaReceipt : Set
    nestedFluxSurfaceReceipt : Set
    divergenceFreeTotalFieldReceipt : Set
    freeBoundaryEquilibriumReceipt : Set

    abcAllocationReceipt : Set
    abcMomentumBalanceOnSameStateReceipt : Set
    flowAndAnisotropyStabilityReceipt : Set
    collisionalKineticClosureReceipt : Set

    zeroBouncePopulationSameObjectReceipt : Set
    equilibriumReference : String

open SameObjectCoilPlasmaEquilibrium public

record ProducedFieldOrbitAcceptance
    {PhysicalState CoilField PlasmaField TotalField : Set}
    {population : ZeroBounce.DeclaredParticlePopulation}
    (eq : SameObjectCoilPlasmaEquilibrium
      PhysicalState CoilField PlasmaField TotalField population) : Set₁ where
  constructor produced-field-orbit-acceptance
  field
    totalFieldUsedForOrbitIntegrationReceipt : Set
    magneticMirrorTurningReceipt : Set
    continuousPassingPopulationReceipt : Set
    trappedFractionReceipt : Set
    parallelInvariantReceipt : Set
    finiteOrbitWidthReceipt : Set
    curvatureAndGradBDriftReceipt : Set
    energeticParticleLossReceipt : Set
    collisionAndTurbulenceRobustnessReceipt : Set
    sameIntegratorSameNormalizationReferenceReceipt : Set
    sameOrBetterBestKnownReferenceReceipt : Set
    acceptanceReference : String

open ProducedFieldOrbitAcceptance public

record SameObjectValidationCoordinates : Set₁ where
  constructor same-object-validation-coordinates
  field
    selectedCoilCurrentConfiguration : Set
    reconstructedExternalField : Set
    reconstructedPlasmaCurrent : Set
    pressureProfile : Set
    flowProfile : Set
    anisotropyProfile : Set
    finiteBetaEquilibrium : Set
    totalFieldReconstruction : Set
    orbitPopulationDefinition : Set
    orbitLossObservation : Set
    sameShotConfigurationReceipt : Set
    coordinateReference : String

open SameObjectValidationCoordinates public

record CoilPlasmaFreeBoundaryBoundary : Set where
  constructor coil-plasma-free-boundary-boundary
  field
    sameObjectFieldSumRequired : Bool
    sameObjectFieldSumRequiredIsTrue : sameObjectFieldSumRequired ≡ true

    coilInverseProxyPaysFreeBoundary : Bool
    coilInverseProxyPaysFreeBoundaryIsFalse :
      coilInverseProxyPaysFreeBoundary ≡ false

    targetSurfaceFieldMayReplaceProducedTotalField : Bool
    targetSurfaceFieldMayReplaceProducedTotalFieldIsFalse :
      targetSurfaceFieldMayReplaceProducedTotalField ≡ false

    abcIdentityAlonePaysKineticEquilibrium : Bool
    abcIdentityAlonePaysKineticEquilibriumIsFalse :
      abcIdentityAlonePaysKineticEquilibrium ≡ false

    producedFieldFullOrbitRequired : Bool
    producedFieldFullOrbitRequiredIsTrue : producedFieldFullOrbitRequired ≡ true

    sameConfigurationReferenceComparisonRequired : Bool
    sameConfigurationReferenceComparisonRequiredIsTrue :
      sameConfigurationReferenceComparisonRequired ≡ true

    acquiredSourceAuthorityTransfersFromNumericalArtifact : Bool
    acquiredSourceAuthorityTransfersFromNumericalArtifactIsFalse :
      acquiredSourceAuthorityTransfersFromNumericalArtifact ≡ false

canonicalCoilPlasmaFreeBoundaryBoundary : CoilPlasmaFreeBoundaryBoundary
canonicalCoilPlasmaFreeBoundaryBoundary =
  coil-plasma-free-boundary-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl

currentMaxCut : String
currentMaxCut =
  "The discrete/periodic-consumer search and proxy coil routing are paid. Remaining payment is physical/execution-bound: solve one same-object finite-beta free-boundary B_total=B_coil+B_plasma equilibrium for each selected Pareto survivor, then integrate the declared population in that produced field and compare with the best-known trapped-particle reference under the same normalization/integrator/configuration."

attributionRule : String
attributionRule =
  "Any acquired experiment, paper, company statement, reconstruction, simulation or benchmark remains role-typed to its source. A source-supported observation does not become artifact authority, and a script-produced field or residual does not become experimental authority. Same-object comparison requires shot/configuration/reconstruction/regime alignment rather than narrative proximity."
