module DASHI.Physics.Plasma.TokamakConfinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement

------------------------------------------------------------------------
-- TOKAMAK SPECIALISATION
--
-- Canonical split:
--   external toroidal field coils
-- + poloidal field from toroidal plasma current / shaping system
-- -> helical field-line cage in an axisymmetric toroidal equilibrium.
--
-- A transformer is a common current-induction mechanism, not part of the
-- mathematical definition: non-inductive current drive remains admissible.
------------------------------------------------------------------------

record TokamakState : Set₁ where
  constructor tokamak-state
  field
    confined : Confinement.MagneticConfinementState
    geometryIsAxisymmetricToroidal :
      Confinement.geometry confined ≡ Confinement.axisymmetricToroidal

    toroidalFieldCoilReceipt : Set
    poloidalFieldSystemReceipt : Set
    netToroidalPlasmaCurrentReceipt : Set
    currentDriveReceipt : Set
    positionShapeControlReceipt : Set
    divertorOrBoundaryControlReceipt : Set

    tokamakReference : String

open TokamakState public

record TokamakEquilibriumReceipt (state : TokamakState) : Set₁ where
  constructor tokamak-equilibrium-receipt
  field
    genericEquilibrium : Confinement.EquilibriumReceipt (confined state)
    gradShafranovAxisymmetricReceipt : Set
    poloidalFluxReceipt : Set
    safetyFactorProfileReceipt : Set
    pressureProfileSameObjectReceipt : Set
    currentProfileSameObjectReceipt : Set
    magneticReconstructionAuthority : Authority.ArtifactAuthorityBoundary
    equilibriumReference : String

open TokamakEquilibriumReceipt public

record TokamakOperationReceipt (state : TokamakState) : Set₁ where
  constructor tokamak-operation-receipt
  field
    equilibrium : TokamakEquilibriumReceipt state
    stability : Confinement.StabilityReceipt (confined state)
    transport : Confinement.TransportReceipt (confined state)
    heatingAndCurrentDriveReceipt : Set
    pulseOrSteadyStateScenarioReceipt : Set
    operationReference : String

open TokamakOperationReceipt public

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

record TokamakBoundary : Set where
  constructor tokamak-boundary
  field
    canonicalTokamakUsesToroidalPlasmaCurrent : Bool
    canonicalTokamakUsesToroidalPlasmaCurrentIsTrue :
      canonicalTokamakUsesToroidalPlasmaCurrent ≡ true

    transformerInductionDefinitionallyRequired : Bool
    transformerInductionDefinitionallyRequiredIsFalse :
      transformerInductionDefinitionallyRequired ≡ false

    axisymmetryAloneProvesGradShafranovEquilibrium : Bool
    axisymmetryAloneProvesGradShafranovEquilibriumIsFalse :
      axisymmetryAloneProvesGradShafranovEquilibrium ≡ false

    gradShafranovEquilibriumAloneProvesStability : Bool
    gradShafranovEquilibriumAloneProvesStabilityIsFalse :
      gradShafranovEquilibriumAloneProvesStability ≡ false

    tokamakTopologyAloneProvesFusionPerformance : Bool
    tokamakTopologyAloneProvesFusionPerformanceIsFalse :
      tokamakTopologyAloneProvesFusionPerformance ≡ false

    steadyStateOperationExcludedByDefinition : Bool
    steadyStateOperationExcludedByDefinitionIsFalse :
      steadyStateOperationExcludedByDefinition ≡ false

canonicalTokamakBoundary : TokamakBoundary
canonicalTokamakBoundary =
  tokamak-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

tokamakPrimaryReference : String
tokamakPrimaryReference =
  "ITER magnetic-confinement/tokamak public technical material; toroidal plus poloidal field gives helical confinement, with plasma current as a tokamak field component"
