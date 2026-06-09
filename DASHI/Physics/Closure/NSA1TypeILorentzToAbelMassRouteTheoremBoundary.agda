module DASHI.Physics.Closure.NSA1TypeILorentzToAbelMassRouteTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

routeBoundaryReference : String
routeBoundaryReference =
  "DASHI.Physics.Closure.NSA1TypeILorentzToAbelMassRouteBoundary"

essAuthorityReference : String
essAuthorityReference =
  "Escauriaza-Seregin-Sverak 2003 compactness / ancient-solution extraction"

data A1TheoremClause : Set where
  typeIToLorentzUniformity : A1TheoremClause
  lorentzToESSCompactness : A1TheoremClause
  dyadicLittlewoodPaleyShellSplit : A1TheoremClause
  localizedShellEnstrophyDefinition : A1TheoremClause
  polarizationStateRecording : A1TheoremClause
  abelTriadicDefectMeasureDefinition : A1TheoremClause
  totalMassBoundByDr : A1TheoremClause
  lambdaMomentTracksDr : A1TheoremClause

canonicalA1TheoremClauses : List A1TheoremClause
canonicalA1TheoremClauses =
  typeIToLorentzUniformity
  ∷ lorentzToESSCompactness
  ∷ dyadicLittlewoodPaleyShellSplit
  ∷ localizedShellEnstrophyDefinition
  ∷ polarizationStateRecording
  ∷ abelTriadicDefectMeasureDefinition
  ∷ totalMassBoundByDr
  ∷ lambdaMomentTracksDr
  ∷ []

a1TheoremClauseCount : Nat
a1TheoremClauseCount = listLength canonicalA1TheoremClauses

a1TheoremClauseCountIs8 : a1TheoremClauseCount ≡ 8
a1TheoremClauseCountIs8 = refl

data A1MeasureProperty : Set where
  finiteMassProperty : A1MeasureProperty
  supportOnSphereTimesIntervalProperty : A1MeasureProperty
  shellAverageNormalizationProperty : A1MeasureProperty
  lambdaMomentIdentityProperty : A1MeasureProperty
  diagnosticPromotionHoldProperty : A1MeasureProperty

canonicalA1MeasureProperties : List A1MeasureProperty
canonicalA1MeasureProperties =
  finiteMassProperty
  ∷ supportOnSphereTimesIntervalProperty
  ∷ shellAverageNormalizationProperty
  ∷ lambdaMomentIdentityProperty
  ∷ diagnosticPromotionHoldProperty
  ∷ []

a1MeasurePropertyCount : Nat
a1MeasurePropertyCount = listLength canonicalA1MeasureProperties

a1MeasurePropertyCountIs5 : a1MeasurePropertyCount ≡ 5
a1MeasurePropertyCountIs5 = refl

data A1TheoremBlocker : Set where
  blocker-essCompactnessWriteupOpen : A1TheoremBlocker
  blocker-shellToMeasureTightnessProofOpen : A1TheoremBlocker
  blocker-lambdaMomentPDEIdentificationOpen : A1TheoremBlocker
  blocker-nsClayPromotionForbidden : A1TheoremBlocker
  blocker-terminalPromotionForbidden : A1TheoremBlocker

canonicalA1TheoremBlockers : List A1TheoremBlocker
canonicalA1TheoremBlockers =
  blocker-essCompactnessWriteupOpen
  ∷ blocker-shellToMeasureTightnessProofOpen
  ∷ blocker-lambdaMomentPDEIdentificationOpen
  ∷ blocker-nsClayPromotionForbidden
  ∷ blocker-terminalPromotionForbidden
  ∷ []

a1TheoremRecorded : Bool
a1TheoremRecorded = true

A1TypeILorentzToAbelMassRouteTheoremProved : Bool
A1TypeILorentzToAbelMassRouteTheoremProved = false

NSClayPromotedFromA1Theorem : Bool
NSClayPromotedFromA1Theorem = false

TerminalPromotedFromA1Theorem : Bool
TerminalPromotedFromA1Theorem = false

record NSA1TypeILorentzToAbelMassRouteTheoremBoundary : Set where
  field
    theoremClauses : List A1TheoremClause
    theoremClausesCanonical : theoremClauses ≡ canonicalA1TheoremClauses
    measureProperties : List A1MeasureProperty
    measurePropertiesCanonical :
      measureProperties ≡ canonicalA1MeasureProperties
    blockers : List A1TheoremBlocker
    blockersCanonical : blockers ≡ canonicalA1TheoremBlockers
    clauseCountIs8 : a1TheoremClauseCount ≡ 8
    propertyCountIs5 : a1MeasurePropertyCount ≡ 5
    theoremStillFalse :
      A1TypeILorentzToAbelMassRouteTheoremProved ≡ false
    nsClayStillFalse : NSClayPromotedFromA1Theorem ≡ false
    terminalStillFalse : TerminalPromotedFromA1Theorem ≡ false

canonicalNSA1TypeILorentzToAbelMassRouteTheoremBoundary :
  NSA1TypeILorentzToAbelMassRouteTheoremBoundary
canonicalNSA1TypeILorentzToAbelMassRouteTheoremBoundary =
  record
    { theoremClauses = canonicalA1TheoremClauses
    ; theoremClausesCanonical = refl
    ; measureProperties = canonicalA1MeasureProperties
    ; measurePropertiesCanonical = refl
    ; blockers = canonicalA1TheoremBlockers
    ; blockersCanonical = refl
    ; clauseCountIs8 = refl
    ; propertyCountIs5 = refl
    ; theoremStillFalse = refl
    ; nsClayStillFalse = refl
    ; terminalStillFalse = refl
    }

a1TheoremRecordedIsTrue : a1TheoremRecorded ≡ true
a1TheoremRecordedIsTrue = refl
