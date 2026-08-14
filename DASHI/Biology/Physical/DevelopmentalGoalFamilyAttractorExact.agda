module DASHI.Biology.Physical.DevelopmentalGoalFamilyAttractorExact where

------------------------------------------------------------------------
-- Source-facing motivation:
-- Michael Levin, "Bioelectric signaling: Reprogrammable circuits underlying
-- embryogenesis, regeneration, and cancer", Cell 184 (2021), 1971-1989.
-- DOI: 10.1016/j.cell.2021.02.034.
--
-- DASHI CONTRIBUTION
-- A developmental goal is interpreted as a constraint family, not a unique
-- microscopic bitmap.  Two distinct fine morphologies can satisfy the same
-- organ/location/owner/side/scale target.  A finite corrective operator repairs
-- a damaged macro-coordinate while preserving an unconstrained micro-detail.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DevelopmentalGoalFactorizationExact as Goal

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

record FineMorphology : Set where
  constructor fineMorphology
  field
    organ : Goal.OrganKind
    anchor : Bool
    owner : Bool
    side : Goal.Side
    scaleClass : Nat
    microDetail : Bool

open FineMorphology public

record SatisfiesGoal (m : FineMorphology) (g : Goal.DevelopmentalGoal) : Set where
  constructor satisfiesGoal
  field
    organMatches : organ m ≡ Goal.organ g
    anchorMatches : anchor m ≡ Goal.anchor g
    ownerMatches : owner m ≡ Goal.owner g
    sideMatches : side m ≡ Goal.side g
    scaleMatches : scaleClass m ≡ Goal.scaleClass g

open SatisfiesGoal public

handMicroA handMicroB : FineMorphology
handMicroA = fineMorphology Goal.hand false false Goal.leftSide 1 false
handMicroB = fineMorphology Goal.hand false false Goal.leftSide 1 true

handMicroA≢handMicroB : handMicroA ≢ handMicroB
handMicroA≢handMicroB eq = false≢true (cong microDetail eq)

handMicroASatisfiesGoal : SatisfiesGoal handMicroA Goal.leftHandHereOurs
handMicroASatisfiesGoal = satisfiesGoal refl refl refl refl refl

handMicroBSatisfiesGoal : SatisfiesGoal handMicroB Goal.leftHandHereOurs
handMicroBSatisfiesGoal = satisfiesGoal refl refl refl refl refl

sameHighLevelGoalHasDistinctFineRealisations :
  Σ FineMorphology (λ left →
    Σ FineMorphology (λ right →
      SatisfiesGoal left Goal.leftHandHereOurs
      × SatisfiesGoal right Goal.leftHandHereOurs
      × left ≢ right))
sameHighLevelGoalHasDistinctFineRealisations =
  handMicroA ,
  (handMicroB ,
    (handMicroASatisfiesGoal ,
      (handMicroBSatisfiesGoal , handMicroA≢handMicroB)))

------------------------------------------------------------------------
-- Goal-conditioned repair changes constrained coordinates but leaves an
-- unconstrained microscopic coordinate untouched.
------------------------------------------------------------------------

repairToGoal : Goal.DevelopmentalGoal → FineMorphology → FineMorphology
repairToGoal g m =
  fineMorphology
    (Goal.organ g)
    (Goal.anchor g)
    (Goal.owner g)
    (Goal.side g)
    (Goal.scaleClass g)
    (microDetail m)

repairSatisfiesGoal :
  (g : Goal.DevelopmentalGoal) (m : FineMorphology) →
  SatisfiesGoal (repairToGoal g m) g
repairSatisfiesGoal g m = satisfiesGoal refl refl refl refl refl

repairPreservesMicroDetail :
  (g : Goal.DevelopmentalGoal) (m : FineMorphology) →
  microDetail (repairToGoal g m) ≡ microDetail m
repairPreservesMicroDetail g m = refl

repairIsIdempotent :
  (g : Goal.DevelopmentalGoal) (m : FineMorphology) →
  repairToGoal g (repairToGoal g m) ≡ repairToGoal g m
repairIsIdempotent g
  (fineMorphology organ anchor owner side scale micro) = refl

-- A damaged anchor can therefore be corrected without forcing a unique fine
-- realization of the target.
damagedHand : FineMorphology
damagedHand = fineMorphology Goal.hand true false Goal.leftSide 1 true

repairDamagedHandHitsOurHandGoal :
  SatisfiesGoal (repairToGoal Goal.leftHandHereOurs damagedHand)
    Goal.leftHandHereOurs
repairDamagedHandHitsOurHandGoal = repairSatisfiesGoal Goal.leftHandHereOurs damagedHand

repairDamagedHandKeepsMicroDetail :
  microDetail (repairToGoal Goal.leftHandHereOurs damagedHand) ≡ true
repairDamagedHandKeepsMicroDetail = refl
