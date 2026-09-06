module DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- VIRIATO NUMERICAL SCIENCE
------------------------------------------------------------------------

data PlasmaModel : Set where
  KREHM KRMHD reducedMHDLimit : PlasmaModel

data ParallelScheme : Set where
  macCormack2
  tvdRK3Upwind7
  : ParallelScheme

data PerpendicularScheme : Set where
  pseudoSpectral
  : PerpendicularScheme

data VelocitySpaceScheme : Set where
  hermiteSpectral
  : VelocitySpaceScheme

data OperatorSplit : Set where
  strang godunov : OperatorSplit

record ViriatoNumericalArchitecture : Set where
  constructor viriato-numerical-architecture
  field
    solvedModels : List PlasmaModel
    splitOptions : List OperatorSplit
    parallelOptions : List ParallelScheme
    perpendicularScheme : PerpendicularScheme
    velocitySpaceScheme : VelocitySpaceScheme
    sourceReference : String

open ViriatoNumericalArchitecture public

canonicalViriatoArchitecture : ViriatoNumericalArchitecture
canonicalViriatoArchitecture = viriato-numerical-architecture
  (KREHM ∷ KRMHD ∷ reducedMHDLimit ∷ [])
  (strang ∷ godunov ∷ [])
  (macCormack2 ∷ tvdRK3Upwind7 ∷ [])
  pseudoSpectral
  hermiteSpectral
  "Loureiro et al., Computer Physics Communications 206 (2016) 45-63, DOI 10.1016/j.cpc.2016.05.004; arXiv:1505.02649"

operatorSplittingReceipt : S.ScientificMechanismReceipt
operatorSplittingReceipt = S.scientific-mechanism-receipt
  "Viriato"
  "parallel and perpendicular dynamics are separated using Strang or Godunov operator splitting under a strong guide-field reduced model"
  S.numericalMethod
  S.sourceBacked
  "Loureiro et al. 2016 / arXiv:1505.02649"
  "Operator splitting is a numerical decomposition of the model evolution; it is not evidence that the physical plasma literally evolves in separated stages."

hermiteReceipt : S.ScientificMechanismReceipt
hermiteReceipt = S.scientific-mechanism-receipt
  "Viriato"
  "parallel velocity-space dependence of the perturbed distribution is represented spectrally using Hermite modes"
  S.numericalMethod
  S.sourceBacked
  "Loureiro et al. 2016 / arXiv:1505.02649"
  "The Hermite representation exposes kinetic phase mixing in a tractable spectral basis; convergence depends on sufficient velocity-space resolution and closure/dissipation choices."

benchmarkReceipt : S.ScientificMechanismReceipt
benchmarkReceipt = S.scientific-mechanism-receipt
  "Viriato"
  "the code is tested with linear and nonlinear benchmarks including two- and three-dimensional Orszag-Tang-type decaying turbulence in fluid and kinetic regimes"
  S.benchmarkOrValidationTest
  S.sourceBacked
  "Loureiro et al. 2016"
  "Agreement on benchmarks validates implementation against selected equations/tests; it does not validate every physical approximation of KREHM/KRMHD for all plasmas."

reducedModelBoundary : S.ScientificMechanismReceipt
reducedModelBoundary = S.scientific-mechanism-receipt
  "KREHM/KRMHD reduced plasma descriptions"
  "Viriato solves reduced strongly magnetised plasma models applicable to turbulence and reconnection in their asymptotic regimes"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "Loureiro et al. 2016"
  "Reduced-model validity is conditional on the ordering assumptions used to derive KREHM/KRMHD; numerical accuracy does not remove model-form error."

viriatoNeedsModelRegimeReceipt : S.ScientificReverseObligation
viriatoNeedsModelRegimeReceipt = S.scientific-reverse-obligation
  "application of Viriato to a physical plasma"
  S.mechanismToObservationWeld
  "show that the target plasma satisfies the reduced-model ordering assumptions and that relevant neglected physics is controlled for the observable of interest"
  "physical applicability of a particular Viriato simulation"
  "universal plasma truth merely from code convergence or benchmark success"

record CurrentViriatoScienceAssessment : Set where
  constructor current-viriato-science-assessment
  field
    modelsOwned : Bool
    modelsOwnedIsTrue : modelsOwned ≡ true
    numericalArchitectureOwned : Bool
    numericalArchitectureOwnedIsTrue : numericalArchitectureOwned ≡ true
    benchmarkSuiteOwned : Bool
    benchmarkSuiteOwnedIsTrue : benchmarkSuiteOwned ≡ true
    universalPhysicalValidityOwned : Bool
    universalPhysicalValidityOwnedIsFalse : universalPhysicalValidityOwned ≡ false

canonicalCurrentViriatoScienceAssessment : CurrentViriatoScienceAssessment
canonicalCurrentViriatoScienceAssessment = current-viriato-science-assessment
  true refl
  true refl
  true refl
  false refl
