module DASHI.Physics.Plasma.ProgrammableTokamakStellaratorHybridExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement
import DASHI.Physics.Plasma.CommercialFusionPlantObjectiveExact as Plant
import DASHI.Physics.Plasma.GreenwaldDensityOperatingEnvelopeBidiExact as Density

------------------------------------------------------------------------
-- PROGRAMMABLE TOKAMAK-STELLARATOR HYBRID CANDIDATE
--
-- Source motivation (not promotion):
--   * J-TEXT 2026 experimentally applies external rotational transform (ERT)
--     to a tokamak and reports tearing-mode suppression / expanded operation;
--   * 2026 programmable planar dipole-field-coil studies exhibit a broad family
--     of tokamak, QA/QH/QI and finite-beta hybrid equilibria from fixed hardware.
--
-- DASHI interpretation: external transform, plasma current, coil programming,
-- wall stabilization and high-field compactness are independent design axes.
------------------------------------------------------------------------

record ProgrammableHybridState : Set₁ where
  constructor programmable-hybrid-state
  field
    confined : Confinement.MagneticConfinementState

    axisymmetricBackboneReceipt : Set
    externalRotationalTransformReceipt : Set
    programmablePlanarCoilArrayReceipt : Set
    finiteBetaFreeBoundaryEquilibriumReceipt : Set
    quasiSymmetryOrOmnigenityReceipt : Set
    bootstrapCurrentReceipt : Set
    reducedDrivenCurrentDemandReceipt : Set
    tearingAndDisruptionStabilityReceipt : Set
    energeticParticleConfinementReceipt : Set
    conductingWallCompatibilityReceipt : Set
    highFieldHTSCompatibilityReceipt : Set
    divertorAndExhaustGeometryReceipt : Set
    blanketAndMaintenanceAccessReceipt : Set
    realTimeConfigurationControlReceipt : Set

    equilibriumAuthority : Authority.ArtifactAuthorityBoundary
    hybridReference : String

open ProgrammableHybridState public

record ProgrammableHybridCommercialCandidate
    (state : ProgrammableHybridState) : Set₁ where
  constructor programmable-hybrid-commercial-candidate
  field
    equilibrium : Confinement.EquilibriumReceipt (confined state)
    stability : Confinement.StabilityReceipt (confined state)
    transport : Confinement.TransportReceipt (confined state)
    densityEnvelope : Density.DensityOperatingEnvelope (confined state)
    plant : Plant.CommercialFusionPlantState (confined state)

    configurationSearchReceipt : Set
    coilCurrentEnvelopeReceipt : Set
    topologyTransitionControlReceipt : Set
    steadyStateReceipt : Set
    commercialReference : String

open ProgrammableHybridCommercialCandidate public

jTextERTSource : String
jTextERTSource =
  "Li et al., Nuclear Fusion 66 (2026) 056013, doi:10.1088/1741-4326/ae51a5"

programmableHybridSource : String
programmableHybridSource =
  "Yu et al., arXiv:2605.03599, A programmable stellarator-tokamak hybrid for million-scale magnetic-configuration discovery"

finiteBetaHybridSource : String
finiteBetaHybridSource =
  "Liang et al., arXiv:2607.14146, Optimized finite-beta tokamak-stellarator hybrid configurations achieved by planar dipole-field coils"

record ProgrammableHybridBoundary : Set where
  constructor programmable-hybrid-boundary
  field
    jTextTearingSuppressionProvesPowerPlantStability : Bool
    jTextTearingSuppressionProvesPowerPlantStabilityIsFalse :
      jTextTearingSuppressionProvesPowerPlantStability ≡ false

    millionMagneticConfigurationsAreMillionCommercialPlants : Bool
    millionMagneticConfigurationsAreMillionCommercialPlantsIsFalse :
      millionMagneticConfigurationsAreMillionCommercialPlants ≡ false

    externalTransformEliminatesAllPlasmaCurrentRequirements : Bool
    externalTransformEliminatesAllPlasmaCurrentRequirementsIsFalse :
      externalTransformEliminatesAllPlasmaCurrentRequirements ≡ false

    programmableCoilsPermitTopologyAsSearchCoordinate : Bool
    programmableCoilsPermitTopologyAsSearchCoordinateIsTrue :
      programmableCoilsPermitTopologyAsSearchCoordinate ≡ true

    hybridMayTradeExternalTransformAgainstDrivenCurrent : Bool
    hybridMayTradeExternalTransformAgainstDrivenCurrentIsTrue :
      hybridMayTradeExternalTransformAgainstDrivenCurrent ≡ true

    commercialSuperiorityStillRequiresPlantLevelReceipt : Bool
    commercialSuperiorityStillRequiresPlantLevelReceiptIsTrue :
      commercialSuperiorityStillRequiresPlantLevelReceipt ≡ true

canonicalProgrammableHybridBoundary : ProgrammableHybridBoundary
canonicalProgrammableHybridBoundary =
  programmable-hybrid-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
