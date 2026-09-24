module DASHI.Physics.Closure.NSOpenAI2026ReleasedDebtSmoothExact where

------------------------------------------------------------------------
-- NATIVE PORT: MeanStageRegularity.debt_smooth dependency decomposition
--
-- Released source computes the three measured debt components from four
-- radial-moment smoothness facts:
--
--   pressure defect : source moment order 0
--   theta defect    : angular-flux axial moment order 2
--   axial defect    : axial-flux axial moment order 1
--                     minus coefficient * source moment order 2
--
-- The functional-analysis proof of those moment-smoothness facts remains a
-- lower leaf.  This module closes the exact component assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ReleasedDebtSmoothSurface : Set₁ where
  field
    SmoothField : Set
    DebtSmooth : Set

    subtractScaled :
      SmoothField → SmoothField → SmoothField

    assembleDebt :
      SmoothField →
      SmoothField →
      SmoothField →
      DebtSmooth

open ReleasedDebtSmoothSurface public

record ReleasedRadialMomentSmoothness
    (S : ReleasedDebtSmoothSurface) : Set₁ where
  field
    sourceMoment0Smooth : SmoothField S
    sourceMoment2Smooth : SmoothField S
    angularFluxAxialMoment2Smooth : SmoothField S
    axialFluxAxialMoment1Smooth : SmoothField S

open ReleasedRadialMomentSmoothness public

record ReleasedDebtSmoothComponents
    (S : ReleasedDebtSmoothSurface) : Set₁ where
  field
    pressureDefectSmooth : SmoothField S
    thetaDefectSmooth : SmoothField S
    axialDefectSmooth : SmoothField S

open ReleasedDebtSmoothComponents public

debtSmoothComponents :
  ∀ {S} →
  ReleasedRadialMomentSmoothness S →
  ReleasedDebtSmoothComponents S
debtSmoothComponents {S} H =
  record
    { pressureDefectSmooth =
        sourceMoment0Smooth H
    ; thetaDefectSmooth =
        angularFluxAxialMoment2Smooth H
    ; axialDefectSmooth =
        subtractScaled S
          (axialFluxAxialMoment1Smooth H)
          (sourceMoment2Smooth H)
    }

debtSmooth :
  ∀ {S} →
  ReleasedRadialMomentSmoothness S →
  DebtSmooth S
debtSmooth {S} H =
  let C = debtSmoothComponents H
  in
  assembleDebt S
    (pressureDefectSmooth C)
    (thetaDefectSmooth C)
    (axialDefectSmooth C)

releasedDebtSmoothAssemblyPorted : Bool
releasedDebtSmoothAssemblyPorted = true

pressureDefectDependencyExact : Bool
pressureDefectDependencyExact = true

thetaDefectDependencyExact : Bool
thetaDefectDependencyExact = true

axialDefectDependencyExact : Bool
axialDefectDependencyExact = true

radialMomentSmoothnessAnalysisPopulatedHere : Bool
radialMomentSmoothnessAnalysisPopulatedHere = false

releasedDebtSmoothAssemblyPortedIsTrue :
  releasedDebtSmoothAssemblyPorted ≡ true
releasedDebtSmoothAssemblyPortedIsTrue = refl

radialMomentSmoothnessAnalysisPopulatedHereIsFalse :
  radialMomentSmoothnessAnalysisPopulatedHere ≡ false
radialMomentSmoothnessAnalysisPopulatedHereIsFalse = refl
