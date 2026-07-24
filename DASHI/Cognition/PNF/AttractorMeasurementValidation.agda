module DASHI.Cognition.PNF.AttractorMeasurementValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PredictiveInverseAttractor as Attractor

record MeasurementContract : Set where
  constructor measurementContract
  field
    instrument population context timeScale : String
    projection errorModel identifiabilityBoundary : String
    spanAndProvenanceRequired : Bool
    spanAndProvenanceRequiredIsTrue : spanAndProvenanceRequired ≡ true

open MeasurementContract public

record NonIdentifiabilityWitness : Set where
  constructor nonIdentifiabilityWitness
  field
    hiddenDescriptionLeft hiddenDescriptionRight : String
    commonObservable : String
    hiddenStatesDistinctReceipt : String

open NonIdentifiabilityWitness public

record AttractorValidationReceipt : Set where
  constructor attractorValidationReceipt
  field
    candidate : Attractor.ResolutionIndexedAttractor
    eventStream : List PNF.EventPNF
    measurement : MeasurementContract
    invariantRegion metric perturbationClass : String
    persistenceHorizon : Nat
    attractionOrRepulsionWitnessed : Bool
    attractionOrRepulsionWitnessedIsTrue :
      attractionOrRepulsionWitnessed ≡ true
    persistenceWitnessed : Bool
    persistenceWitnessedIsTrue : persistenceWitnessed ≡ true
    resolutionDependenceWitnessed : Bool
    resolutionDependenceWitnessedIsTrue : resolutionDependenceWitnessed ≡ true
    contextDependenceWitnessed : Bool
    contextDependenceWitnessedIsTrue : contextDependenceWitnessed ≡ true
    performativeSignWitnessed : Bool
    performativeSignWitnessedIsTrue : performativeSignWitnessed ≡ true
    validationReceiptId : String

open AttractorValidationReceipt public

record AttractorAuthorityBoundary : Set where
  constructor attractorAuthorityBoundary
  field
    finiteBankRunFixtureIsEmpiricalBankTheorem : Bool
    finiteBankRunFixtureIsEmpiricalBankTheoremIsFalse :
      finiteBankRunFixtureIsEmpiricalBankTheorem ≡ false
    embeddingOrSentimentAloneValidatesAttractor : Bool
    embeddingOrSentimentAloneValidatesAttractorIsFalse :
      embeddingOrSentimentAloneValidatesAttractor ≡ false

canonicalAttractorAuthorityBoundary : AttractorAuthorityBoundary
canonicalAttractorAuthorityBoundary =
  attractorAuthorityBoundary false refl false refl
