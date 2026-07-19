module DASHI.Biology.Levin.LatentPatternInterfaceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.EffortOutcomeAccounting as Accounting
import DASHI.Biology.Levin.PolycomputationBiologyAdapter as Poly
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden

------------------------------------------------------------------------
-- A latent-pattern interpretation is represented as a hypothesis about an
-- interface, never as a consequence of surprising behaviour alone.

record PatternInterfaceModel : Set where
  field
    physicalCarrier       : Bool
    admissiblePatternClass : Bool
    couplingLawSpecified  : Bool
    exclusionPredictions  : Bool
    interventionProtocol  : Bool
    competingModelsListed : Bool
    quantitativeFit       : Bool
    outOfSamplePrediction : Bool
    interpretation        : String

record LatentPatternPromotionGate : Set where
  field
    effortAccounting : Accounting.ResidualExplanationBoundary
    polycomputationBoundary : Poly.PolycomputationBiologyAdapter
    boundaryUnderdeterminationAcknowledged : Bool
    physicalMechanismNotExcludedBySurprise : Bool
    metaphysicalReadingOptional : Bool
    empiricalProgrammeRequired : Bool
    promotionAllowed : Bool

canonicalPatternInterfaceModel : PatternInterfaceModel
canonicalPatternInterfaceModel = record
  { physicalCarrier = true
  ; admissiblePatternClass = false
  ; couplingLawSpecified = false
  ; exclusionPredictions = false
  ; interventionProtocol = false
  ; competingModelsListed = true
  ; quantitativeFit = false
  ; outOfSamplePrediction = false
  ; interpretation = "A latent-pattern interface becomes scientific only through a typed coupling law, interventions, exclusions, and successful prediction"
  }

MathematicalTruthImpliesSeparateCausalRealm : Bool
MathematicalTruthImpliesSeparateCausalRealm = false

SurprisingCompetenceImpliesPatternIngress : Bool
SurprisingCompetenceImpliesPatternIngress = false

FormalModelExhaustsPhysicalSystem : Bool
FormalModelExhaustsPhysicalSystem = false
