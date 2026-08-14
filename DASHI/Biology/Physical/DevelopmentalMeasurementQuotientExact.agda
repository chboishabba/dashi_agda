module DASHI.Biology.Physical.DevelopmentalMeasurementQuotientExact where

------------------------------------------------------------------------
-- Biological measurements are projections.  Equal transcript observation does
-- not imply equal developmental future when chromatin/bioelectric state differs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

record CellState : Set where
  constructor cellState
  field
    genome : Bool
    transcript : Bool
    chromatin : Bool
    bioelectric : Bool
    phenotype : Bool

open CellState public

cellUpdate : CellState → CellState
cellUpdate (cellState g t c b p) =
  cellState g t c b (xor p (xor c b))

transcriptObservation : CellState → Bool
transcriptObservation = transcript

phenotypeObservation : CellState → Bool
phenotypeObservation = phenotype

data Action : Set where
  develop : Action

system : Dependency.DependentActionSystem CellState Action
system = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ cellUpdate before
  ; actionLabel = λ action → "develop"
  }

admissible : (x : CellState) → Dependency.AdmissibleAction system x develop
admissible x = record
  { precondition = tt
  ; after = cellUpdate x
  ; postcondition = refl
  ; dependencyReceipt = "deterministic cell-state update"
  }

left right : CellState
left = cellState false false false false false
right = cellState false false true false false

sameGenome : genome left ≡ genome right
sameGenome = refl

sameTranscript : transcriptObservation left ≡ transcriptObservation right
sameTranscript = refl

samePresentPhenotype : phenotypeObservation left ≡ phenotypeObservation right
samePresentPhenotype = refl

futurePhenotypesDiffer :
  phenotypeObservation (cellUpdate left) ≢ phenotypeObservation (cellUpdate right)
futurePhenotypesDiffer = false≢true

leftRun : Reachability.Executes system (develop ∷ []) left (cellUpdate left)
leftRun = Reachability.executesCons (admissible left) Reachability.executesNil

rightRun : Reachability.Executes system (develop ∷ []) right (cellUpdate right)
rightRun = Reachability.executesCons (admissible right) Reachability.executesNil

phenotypeProjectionDynamicDefect :
  Dynamic.TerminalisationDefect system phenotypeObservation
phenotypeProjectionDynamicDefect = record
  { actionTrace = develop ∷ []
  ; left = left
  ; right = right
  ; leftAfter = cellUpdate left
  ; rightAfter = cellUpdate right
  ; sameCurrentObservation = refl
  ; leftExecution = leftRun
  ; rightExecution = rightRun
  ; futureObservationsDiffer = futurePhenotypesDiffer
  }

phenotypeOnlyNotFutureSafe :
  Dynamic.DynamicConsumerSafety system phenotypeObservation → ⊥
phenotypeOnlyNotFutureSafe safety =
  Dynamic.terminalisationDefectContradictsSafety safety phenotypeProjectionDynamicDefect

-- The same witnesses simultaneously show that genome + transcript equality is
-- insufficient to reconstruct the fine biological state used by this update.
record SameMeasuredDifferentHidden : Set where
  field
    measuredGenomeEqual : genome left ≡ genome right
    measuredTranscriptEqual : transcript left ≡ transcript right
    hiddenChromatinDifferent : chromatin left ≢ chromatin right

canonicalSameMeasuredDifferentHidden : SameMeasuredDifferentHidden
canonicalSameMeasuredDifferentHidden = record
  { measuredGenomeEqual = refl
  ; measuredTranscriptEqual = refl
  ; hiddenChromatinDifferent = false≢true
  }
