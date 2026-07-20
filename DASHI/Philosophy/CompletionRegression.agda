module DASHI.Philosophy.CompletionRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Philosophy.ClosureKinds as Closure
import DASHI.Philosophy.CulturalProvenanceAdapter as Cultural
import DASHI.Philosophy.JustifiedRefusal as Refusal
import DASHI.Philosophy.LocalChartLaws as Chart
import DASHI.Philosophy.MaterialLeverageClosure as Leverage
import DASHI.Philosophy.MentalHealthWorkedExample as Mental
import DASHI.Philosophy.RepairCalculus as Repair
import DASHI.Philosophy.ResidualStatus as Residual

data Point : Set where
  point : Point

data Coordinate : Set where
  coordinate : Coordinate

pointChart : Chart.InvertibleChart Point Coordinate
pointChart =
  record
    { Chart.normalise = λ _ → coordinate
    ; Chart.denormalise = λ _ → point
    ; Chart.denormaliseAfterNormalise = λ _ → refl
    ; Chart.normaliseAfterDenormalise = λ _ → refl
    }

chartIdentityRegression :
  Chart.transition pointChart pointChart coordinate ≡ coordinate
chartIdentityRegression = Chart.transitionIdentity pointChart coordinate

chartCocycleRegression :
  Chart.transition pointChart pointChart
    (Chart.transition pointChart pointChart coordinate)
  ≡ Chart.transition pointChart pointChart coordinate
chartCocycleRegression =
  Chart.transitionCocycle pointChart pointChart pointChart coordinate

stageNineRemainsProvisional :
  Closure.stageNineIsFinalTruth Closure.canonicalClosureBoundary ≡ false
stageNineRemainsProvisional = refl

refusalIsNotClosedMindedness :
  Refusal.everyRefusalIsClosedMinded Refusal.canonicalRefusalBoundary ≡ false
refusalIsNotClosedMindedness = refl

repairIsNotReturn :
  Repair.repairEqualsReturn Repair.canonicalRepairBoundary ≡ false
repairIsNotReturn = refl

residualNeedNotVanish :
  Residual.everyResidualShouldVanish Residual.canonicalResidualBoundary ≡ false
residualNeedNotVanish = refl

changedFeedbackNotAutomaticTopology :
  Leverage.changedFeedbackAutomaticallyChangesTopology
    Leverage.canonicalLeverageClosureBoundary
  ≡ false
changedFeedbackNotAutomaticTopology = refl

inspirationDoesNotRepresent :
  Cultural.representsTradition Cultural.canonicalPhilosophyCulturalAdapter ≡ false
inspirationDoesNotRepresent = refl

mentalHealthDoesNotAutoDiagnose :
  Mental.automaticDiagnosisInferred Mental.canonicalMentalHealthCase ≡ false
mentalHealthDoesNotAutoDiagnose = refl

mentalHealthDoesNotAutoProveSystem :
  Mental.automaticSystemicTruthInferred Mental.canonicalMentalHealthCase ≡ false
mentalHealthDoesNotAutoProveSystem = refl
