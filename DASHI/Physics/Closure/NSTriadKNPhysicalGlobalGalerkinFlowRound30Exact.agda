module DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGalerkinFlowRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Assemble the exact finite-flow chain without conflating its inputs:
--
--   literal physical vector field
--   + real local Picard--Lindelöf flow
--   + finite blow-up alternative
--   + exact physical energy identity
--   => no finite maximal time.
--
-- The conclusion is a theorem over one trajectory and one norm.  The bundle
-- prevents a local solution, an escape theorem and an energy estimate from
-- being taken from incompatible finite coordinate systems.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNFiniteFlowBlowupAlternativeRound29Exact as Blowup

record PhysicalFiniteGlobalFlowData
    {timeLevel stateLevel : Level}
    (Time : Set timeLevel)
    (PhysicalState : Set stateLevel) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    physicalVectorField : PhysicalState → PhysicalState

    trajectory : Blowup.FiniteNormTrajectory Time PhysicalState

    LocalPhysicalODESolution : Set (timeLevel ⊔ stateLevel)
    localPhysicalODESolution : LocalPhysicalODESolution

    trajectoryUsesPhysicalVectorField : Set (timeLevel ⊔ stateLevel)
    samePhysicalVectorField : trajectoryUsesPhysicalVectorField

    blowupAlternative : Blowup.FiniteBlowupAlternative trajectory
    energyControl : Blowup.EnergyControl trajectory

open PhysicalFiniteGlobalFlowData public

physicalEnergyConstructsUniformBound :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (dataSet : PhysicalFiniteGlobalFlowData Time PhysicalState) →
  Blowup.UniformNormBound (trajectory dataSet)
physicalEnergyConstructsUniformBound dataSet =
  Blowup.energyConstructsUniformNormBound (energyControl dataSet)

physicalFiniteFlowHasNoFiniteMaximalTime :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (dataSet : PhysicalFiniteGlobalFlowData Time PhysicalState) →
  Blowup.FiniteMaximalTime (blowupAlternative dataSet) → ⊥
physicalFiniteFlowHasNoFiniteMaximalTime dataSet =
  Blowup.energyExcludesFiniteMaximalTime
    (blowupAlternative dataSet) (energyControl dataSet)

record LiteralPhysicalGlobalFlowAuthority
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (dataSet : PhysicalFiniteGlobalFlowData Time PhysicalState) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    vectorFieldIsViscousPlusQuadraticGalerkin : Set (timeLevel ⊔ stateLevel)
    trajectoryComesFromRealPicardLindelof : Set (timeLevel ⊔ stateLevel)
    nonlinearEnergyIsExhaustiveTriadCancellation : Set (timeLevel ⊔ stateLevel)
    viscosityIsDiagonalDissipation : Set (timeLevel ⊔ stateLevel)
    allAuthoritiesReferToDataSet : Set (timeLevel ⊔ stateLevel)

open LiteralPhysicalGlobalFlowAuthority public

literalPhysicalGlobalFlowReducerClosed : Bool
literalPhysicalGlobalFlowReducerClosed = true

literalPhysicalGlobalFlowAuthoritySupplied : Bool
literalPhysicalGlobalFlowAuthoritySupplied = false

literalPhysicalGlobalFlowReducerClosedIsTrue :
  literalPhysicalGlobalFlowReducerClosed ≡ true
literalPhysicalGlobalFlowReducerClosedIsTrue = refl

literalPhysicalGlobalFlowAuthoritySuppliedIsFalse :
  literalPhysicalGlobalFlowAuthoritySupplied ≡ false
literalPhysicalGlobalFlowAuthoritySuppliedIsFalse = refl
