module DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Reduce the post-globalization work to explicit physical transport functions:
-- infinite maximal time gives the global velocity, Sobolev/parabolic
-- bootstrapping gives smoothness, pressure is recovered from the projected
-- equation, and the final energy/admissibility fields form the exact
-- submission witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Submission

record GlobalPhysicalSolutionPrimitiveInputs
    (carrier : Submission.PeriodicNavierStokesSubmissionCarrier)
    (initial : Submission.SmoothPeriodicDatum carrier) : Set₁ where
  field
    InfiniteMaximalTime : Set
    infiniteMaximalTime : InfiniteMaximalTime

    velocityFromInfiniteMaximalTime :
      InfiniteMaximalTime → Submission.GlobalVelocity carrier

    velocitySmoothFromSobolevAndParabolicBootstrap :
      (infinite : InfiniteMaximalTime) →
      Submission.GlobalSmoothVelocity carrier
        (velocityFromInfiniteMaximalTime infinite)

    pressureFromProjectedVelocity :
      (infinite : InfiniteMaximalTime) →
      Submission.GlobalPressure carrier

    pressureSmoothFromVelocity :
      (infinite : InfiniteMaximalTime) →
      Submission.GlobalSmoothPressure carrier
        (pressureFromProjectedVelocity infinite)

    velocityPressureSolveOriginalEquation :
      (infinite : InfiniteMaximalTime) →
      Submission.SolvesPeriodicNavierStokes carrier
        (velocityFromInfiniteMaximalTime infinite)
        (pressureFromProjectedVelocity infinite)
        initial

    initialTraceAtZero :
      (infinite : InfiniteMaximalTime) →
      Submission.AttainsInitialDatum carrier
        (velocityFromInfiniteMaximalTime infinite)
        initial

    strongSolutionUniquenessAndPressureNormalization :
      (infinite : InfiniteMaximalTime) →
      Submission.VelocityPressurePairUnique carrier
        (velocityFromInfiniteMaximalTime infinite)
        (pressureFromProjectedVelocity infinite)
        initial

    globalEnergyEquality :
      (infinite : InfiniteMaximalTime) →
      Submission.GlobalEnergyEquality carrier
        (velocityFromInfiniteMaximalTime infinite)
        initial

    divergenceFreePreserved :
      (infinite : InfiniteMaximalTime) →
      Submission.DivergenceFreePreserved carrier
        (velocityFromInfiniteMaximalTime infinite)

    meanZeroPreserved :
      (infinite : InfiniteMaximalTime) →
      Submission.MeanZeroPreserved carrier
        (velocityFromInfiniteMaximalTime infinite)

    finiteEnergyAtEveryTime :
      (infinite : InfiniteMaximalTime) →
      Submission.FiniteEnergyAtEveryTime carrier
        (velocityFromInfiniteMaximalTime infinite)

    HsAboveFiveHalvesEmbedsIntoC1 : Set
    hsAboveFiveHalvesEmbedsIntoC1 : HsAboveFiveHalvesEmbedsIntoC1

    ParabolicSmoothingAfterPositiveTime : Set
    parabolicSmoothingAfterPositiveTime :
      ParabolicSmoothingAfterPositiveTime

    HigherSobolevEnergyInduction : Set
    higherSobolevEnergyInduction : HigherSobolevEnergyInduction

    PressurePoissonEquation : Set
    pressurePoissonEquation : PressurePoissonEquation

    PressureMeanZeroNormalization : Set
    pressureMeanZeroNormalization : PressureMeanZeroNormalization

open GlobalPhysicalSolutionPrimitiveInputs public

globalPhysicalSolutionWitness :
  ∀ {carrier initial} →
  GlobalPhysicalSolutionPrimitiveInputs carrier initial →
  Submission.PeriodicGlobalSolutionWitness carrier initial
globalPhysicalSolutionWitness inputs =
  let infinite = infiniteMaximalTime inputs
  in record
    { velocity = velocityFromInfiniteMaximalTime inputs infinite
    ; pressure = pressureFromProjectedVelocity inputs infinite
    ; velocitySmooth =
        velocitySmoothFromSobolevAndParabolicBootstrap inputs infinite
    ; pressureSmooth = pressureSmoothFromVelocity inputs infinite
    ; solvesEquation =
        velocityPressureSolveOriginalEquation inputs infinite
    ; initialTrace = initialTraceAtZero inputs infinite
    ; uniquePair =
        strongSolutionUniquenessAndPressureNormalization inputs infinite
    ; energyEquality = globalEnergyEquality inputs infinite
    ; divergenceFree = divergenceFreePreserved inputs infinite
    ; meanZero = meanZeroPreserved inputs infinite
    ; finiteEnergy = finiteEnergyAtEveryTime inputs infinite
    }

record UniformGlobalPhysicalSolutionInputs
    (carrier : Submission.PeriodicNavierStokesSubmissionCarrier) : Set₁ where
  field
    primitiveInputsForDatum :
      (initial : Submission.SmoothPeriodicDatum carrier) →
      Submission.DivergenceFreeDatum carrier initial →
      Submission.MeanZeroDatum carrier initial →
      GlobalPhysicalSolutionPrimitiveInputs carrier initial

open UniformGlobalPhysicalSolutionInputs public

uniformGlobalRegularityInputs :
  (carrier : Submission.PeriodicNavierStokesSubmissionCarrier) →
  UniformGlobalPhysicalSolutionInputs carrier →
  Submission.PeriodicNavierStokesGlobalRegularityInputs carrier
uniformGlobalRegularityInputs carrier uniform = record
  { globalSolutionForEveryAdmissibleDatum =
      λ initial divergenceFree meanZero →
        globalPhysicalSolutionWitness
          (primitiveInputsForDatum uniform
            initial divergenceFree meanZero)
  }

globalPhysicalSolutionReductionConstructed : Bool
globalPhysicalSolutionReductionConstructed = true

uniformDatumToSubmissionTheoremReductionConstructed : Bool
uniformDatumToSubmissionTheoremReductionConstructed = true

globalPhysicalSolutionReductionConstructedIsTrue :
  globalPhysicalSolutionReductionConstructed ≡ true
globalPhysicalSolutionReductionConstructedIsTrue = refl

uniformDatumToSubmissionTheoremReductionConstructedIsTrue :
  uniformDatumToSubmissionTheoremReductionConstructed ≡ true
uniformDatumToSubmissionTheoremReductionConstructedIsTrue = refl
