module DASHI.Physics.Closure.NSSprint87DangerShellSupFactorizationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt
  as DangerShell
import DASHI.Physics.Closure.NSSprint86KStarHHalfTailObstructionReceipt
  as Sprint86

------------------------------------------------------------------------
-- Sprint 87 NS dyadic sup-factorization receipt.
--
-- The sprint-87 lane closes the formal dyadic supremum bookkeeping needed to
-- split the danger-shell high-high contribution into a shell supremum factor
-- and an H^1 tail factor.  It records that this bookkeeping is enough to
-- express the high-high H^-1/2 bound, but it is not enough to absorb the term:
-- the required strict smallness condition at the danger shell remains false.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

dyadicSupFactorizationClosed : Bool
dyadicSupFactorizationClosed = true

shellSupControlledByH1TailClosed : Bool
shellSupControlledByH1TailClosed = true

highHighHminusHalfBoundClosed : Bool
highHighHminusHalfBoundClosed = true

dangerShellAbsorptionConditionClosed : Bool
dangerShellAbsorptionConditionClosed = false

data DyadicSupFactorizationIngredient : Set where
  littlewoodPaleyDyadicShells :
    DyadicSupFactorizationIngredient
  highHighFrequencyLocality :
    DyadicSupFactorizationIngredient
  shellSupPulledOutsideSum :
    DyadicSupFactorizationIngredient
  hOneTailControlsWeightedShellSup :
    DyadicSupFactorizationIngredient
  hminusHalfDualPairingTarget :
    DyadicSupFactorizationIngredient

canonicalDyadicSupFactorizationIngredients :
  List DyadicSupFactorizationIngredient
canonicalDyadicSupFactorizationIngredients =
  littlewoodPaleyDyadicShells
  ∷ highHighFrequencyLocality
  ∷ shellSupPulledOutsideSum
  ∷ hOneTailControlsWeightedShellSup
  ∷ hminusHalfDualPairingTarget
  ∷ []

data DangerShellSupFactorizationClosedStep : Set where
  dyadicSupFactorizationStep :
    DangerShellSupFactorizationClosedStep
  shellSupControlledByH1TailStep :
    DangerShellSupFactorizationClosedStep
  highHighHminusHalfBoundStep :
    DangerShellSupFactorizationClosedStep

canonicalClosedSteps :
  List DangerShellSupFactorizationClosedStep
canonicalClosedSteps =
  dyadicSupFactorizationStep
  ∷ shellSupControlledByH1TailStep
  ∷ highHighHminusHalfBoundStep
  ∷ []

data DangerShellSupFactorizationOpenBoundary : Set where
  strictDangerShellSmallnessCoefficient :
    DangerShellSupFactorizationOpenBoundary
  epsilonBelowOneAbsorptionAtKStar :
    DangerShellSupFactorizationOpenBoundary
  kstarHHalfTailSmallnessWithoutHiddenRegularity :
    DangerShellSupFactorizationOpenBoundary
  thetaBKMContinuationFromRealNSEvolution :
    DangerShellSupFactorizationOpenBoundary
  clayNavierStokesPromotion :
    DangerShellSupFactorizationOpenBoundary

canonicalOpenBoundaries :
  List DangerShellSupFactorizationOpenBoundary
canonicalOpenBoundaries =
  strictDangerShellSmallnessCoefficient
  ∷ epsilonBelowOneAbsorptionAtKStar
  ∷ kstarHHalfTailSmallnessWithoutHiddenRegularity
  ∷ thetaBKMContinuationFromRealNSEvolution
  ∷ clayNavierStokesPromotion
  ∷ []

data DyadicSupFactorizationWitness : Set where
  highHighShellSupTimesHOneTail :
    DyadicSupFactorizationWitness

data ShellSupControlledByH1TailWitness : Set where
  weightedShellSupBoundedByHOneTail :
    ShellSupControlledByH1TailWitness

data HighHighHminusHalfBoundWitness : Set where
  hminusHalfHighHighBoundFromSupFactorization :
    DyadicSupFactorizationWitness →
    ShellSupControlledByH1TailWitness →
    HighHighHminusHalfBoundWitness

canonicalDyadicSupFactorizationWitness :
  DyadicSupFactorizationWitness
canonicalDyadicSupFactorizationWitness =
  highHighShellSupTimesHOneTail

canonicalShellSupControlledByH1TailWitness :
  ShellSupControlledByH1TailWitness
canonicalShellSupControlledByH1TailWitness =
  weightedShellSupBoundedByHOneTail

canonicalHighHighHminusHalfBoundWitness :
  HighHighHminusHalfBoundWitness
canonicalHighHighHminusHalfBoundWitness =
  hminusHalfHighHighBoundFromSupFactorization
    canonicalDyadicSupFactorizationWitness
    canonicalShellSupControlledByH1TailWitness

dyadicSupFactorizationFormula : String
dyadicSupFactorizationFormula =
  "High-high shell sum is factored as sup_j shellWeight(j,t) times the H^1 tail square/sum over dyadic shells above K*(t)."

shellSupH1TailFormula : String
shellSupH1TailFormula =
  "The dyadic shell supremum is bounded by the recorded H^1 tail weight, with no Serrin, BKM, or H^1 continuation shortcut imported."

highHighHminusHalfBoundFormula : String
highHighHminusHalfBoundFormula =
  "The H^-1/2 high-high contribution is bounded by the dyadic sup factorization and the H^1 tail control surface."

dangerShellAbsorptionBoundary : String
dangerShellAbsorptionBoundary =
  "The absorption condition remains false: Sprint 87 closes the dyadic sup-factorization bookkeeping and the formal H^-1/2 high-high bound, but does not prove epsilon<1 at the danger shell, does not overcome the Sprint 86 KStar-to-H^{1/2} tail obstruction, and does not promote Clay Navier-Stokes."

record NSSprint87DangerShellSupFactorizationReceipt : Setω where
  field
    sprint86Receipt :
      Sprint86.NSSprint86KStarHHalfTailObstructionReceipt
    sprint86NoClay :
      Sprint86.clayNavierStokesPromoted ≡ false
    sprint86AbsorptionStillOpen :
      Sprint86.epsilonBelowOneCoefficientDerivedInRepo ≡ false
    sprint86HighHighDefectStillOpen :
      Sprint86.hminusHalfHighHighDefectTheoremDerivedInRepo ≡ false

    dangerShellMaximumPrincipleReceipt :
      DangerShell.NSDangerShellMaximumPrincipleReceipt
    dangerShellMaximumPrincipleStillOpen :
      DangerShell.dangerShellMaxPrincipleProved
        dangerShellMaximumPrincipleReceipt
      ≡ false

    ingredients :
      List DyadicSupFactorizationIngredient
    ingredientsAreCanonical :
      ingredients ≡ canonicalDyadicSupFactorizationIngredients

    closedSteps :
      List DangerShellSupFactorizationClosedStep
    closedStepsAreCanonical :
      closedSteps ≡ canonicalClosedSteps

    openBoundaries :
      List DangerShellSupFactorizationOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalOpenBoundaries

    dyadicSupFactorizationWitness :
      DyadicSupFactorizationWitness
    dyadicSupFactorizationWitnessIsCanonical :
      dyadicSupFactorizationWitness
      ≡ canonicalDyadicSupFactorizationWitness

    shellSupControlledByH1TailWitness :
      ShellSupControlledByH1TailWitness
    shellSupControlledByH1TailWitnessIsCanonical :
      shellSupControlledByH1TailWitness
      ≡ canonicalShellSupControlledByH1TailWitness

    highHighHminusHalfBoundWitness :
      HighHighHminusHalfBoundWitness
    highHighHminusHalfBoundWitnessIsCanonical :
      highHighHminusHalfBoundWitness
      ≡ canonicalHighHighHminusHalfBoundWitness

    dyadicSupFactorizationClosedIsTrue :
      dyadicSupFactorizationClosed ≡ true
    shellSupControlledByH1TailClosedIsTrue :
      shellSupControlledByH1TailClosed ≡ true
    highHighHminusHalfBoundClosedIsTrue :
      highHighHminusHalfBoundClosed ≡ true
    dangerShellAbsorptionConditionClosedIsFalse :
      dangerShellAbsorptionConditionClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    dyadicSupFactorizationStatement :
      String
    dyadicSupFactorizationStatementIsCanonical :
      dyadicSupFactorizationStatement ≡ dyadicSupFactorizationFormula

    shellSupH1TailStatement :
      String
    shellSupH1TailStatementIsCanonical :
      shellSupH1TailStatement ≡ shellSupH1TailFormula

    highHighHminusHalfBoundStatement :
      String
    highHighHminusHalfBoundStatementIsCanonical :
      highHighHminusHalfBoundStatement ≡ highHighHminusHalfBoundFormula

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ dangerShellAbsorptionBoundary

open NSSprint87DangerShellSupFactorizationReceipt public

canonicalNSSprint87DangerShellSupFactorizationReceipt :
  NSSprint87DangerShellSupFactorizationReceipt
canonicalNSSprint87DangerShellSupFactorizationReceipt =
  record
    { sprint86Receipt =
        Sprint86.canonicalNSSprint86KStarHHalfTailObstructionReceipt
    ; sprint86NoClay =
        refl
    ; sprint86AbsorptionStillOpen =
        refl
    ; sprint86HighHighDefectStillOpen =
        refl
    ; dangerShellMaximumPrincipleReceipt =
        DangerShell.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellMaximumPrincipleStillOpen =
        refl
    ; ingredients =
        canonicalDyadicSupFactorizationIngredients
    ; ingredientsAreCanonical =
        refl
    ; closedSteps =
        canonicalClosedSteps
    ; closedStepsAreCanonical =
        refl
    ; openBoundaries =
        canonicalOpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; dyadicSupFactorizationWitness =
        canonicalDyadicSupFactorizationWitness
    ; dyadicSupFactorizationWitnessIsCanonical =
        refl
    ; shellSupControlledByH1TailWitness =
        canonicalShellSupControlledByH1TailWitness
    ; shellSupControlledByH1TailWitnessIsCanonical =
        refl
    ; highHighHminusHalfBoundWitness =
        canonicalHighHighHminusHalfBoundWitness
    ; highHighHminusHalfBoundWitnessIsCanonical =
        refl
    ; dyadicSupFactorizationClosedIsTrue =
        refl
    ; shellSupControlledByH1TailClosedIsTrue =
        refl
    ; highHighHminusHalfBoundClosedIsTrue =
        refl
    ; dangerShellAbsorptionConditionClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; dyadicSupFactorizationStatement =
        dyadicSupFactorizationFormula
    ; dyadicSupFactorizationStatementIsCanonical =
        refl
    ; shellSupH1TailStatement =
        shellSupH1TailFormula
    ; shellSupH1TailStatementIsCanonical =
        refl
    ; highHighHminusHalfBoundStatement =
        highHighHminusHalfBoundFormula
    ; highHighHminusHalfBoundStatementIsCanonical =
        refl
    ; boundary =
        dangerShellAbsorptionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalSprint87Flags :
  (dyadicSupFactorizationClosed ≡ true)
  × (shellSupControlledByH1TailClosed ≡ true)
  × (highHighHminusHalfBoundClosed ≡ true)
  × (dangerShellAbsorptionConditionClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint87Flags =
  refl , refl , refl , refl , refl
