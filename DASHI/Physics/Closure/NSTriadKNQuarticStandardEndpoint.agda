module DASHI.Physics.Closure.NSTriadKNQuarticStandardEndpoint where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Venue/year: Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
-- Uses: Galerkin/compactness existence architecture.
-- Relationship: adapts the standard approximation-and-limit route to the
-- official periodic coefficient system.
--
-- Author: Jacques Simon.
-- Title: "Compact sets in the space L^p(0,T;B)".
-- Venue/year: Annali di Matematica Pura ed Applicata 146 (1987), 65--96.
-- DOI: 10.1007/BF01762360.
-- Uses: compactness from space bounds and time regularity.
-- Relationship: adapts the Aubin--Lions--Simon compactness endpoint.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the breakdown of smooth solutions for the 3-D Euler
-- equations".
-- Venue/year: Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
-- Uses: vorticity continuation endpoint.
-- Relationship: adapts the criterion after uniform Galerkin expenditure.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGalerkinGlobalRegularityCompletion as Global
import DASHI.Physics.Closure.NSTriadKNGalerkinCompletionEndpoint as Endpoint

record QuarticEightStageEndpointInputs
    {i c t g l s : Level}
    (InitialData : Set i)
    (Cutoff : Set c)
    (Time : Set t)
    (GalerkinState : Set g)
    (LimitState : Set l)
    (Scalar : Set s) :
    Set (lsuc (i ⊔ c ⊔ t ⊔ g ⊔ l ⊔ s)) where
  field
    completion :
      Global.GalerkinGlobalCompletion
        InitialData Cutoff Time GalerkinState LimitState Scalar

    uniformBKMDischargesContinuation :
      ∀ u0 →
      Global.AdmissibleInitialData completion u0 →
      Global.SmoothInitialData completion u0 →
      Global.DivergenceFreeInitialData completion u0 →
      Global.UniformAprioriEstimate completion u0

    compactnessUsesUniformTailAndTimeDerivative : Set
    nonlinearLimitIdentificationUsesStrongConvergence : Set
    projectedInitialDataRecovered : Set
    smoothnessBootstrapAtEveryOrder : Set
    uniquenessByDifferenceEnergyAndGronwall : Set
    exactPeriodicEquationMatched : Set

open QuarticEightStageEndpointInputs public

quarticEightStageInputsImplyClayPeriodic :
  ∀ {i c t g l s}
    {InitialData : Set i}
    {Cutoff : Set c}
    {Time : Set t}
    {GalerkinState : Set g}
    {LimitState : Set l}
    {Scalar : Set s} →
  QuarticEightStageEndpointInputs
    InitialData Cutoff Time GalerkinState LimitState Scalar →
  Global.ClayPeriodicExistenceAndSmoothness
    InitialData Time LimitState
quarticEightStageInputsImplyClayPeriodic inputs =
  Endpoint.galerkinCompletionImpliesClayPeriodic
    (completion inputs)

standardEndpointCompositionImplemented : Bool
standardEndpointCompositionImplemented = true

standardEndpointCompositionImplementedIsTrue :
  standardEndpointCompositionImplemented ≡ true
standardEndpointCompositionImplementedIsTrue = refl

officialPeriodicEndpointInhabited : Bool
officialPeriodicEndpointInhabited = false

officialPeriodicEndpointInhabitedIsFalse :
  officialPeriodicEndpointInhabited ≡ false
officialPeriodicEndpointInhabitedIsFalse = refl
