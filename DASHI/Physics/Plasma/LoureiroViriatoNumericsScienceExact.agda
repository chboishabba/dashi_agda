module DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

data PlasmaModel : Set where KREHM KRMHD reducedMHDLimit : PlasmaModel
data ParallelScheme : Set where macCormack2 tvdRK3Upwind7 : ParallelScheme
data PerpendicularScheme : Set where pseudoSpectral : PerpendicularScheme
data VelocitySpaceScheme : Set where hermiteSpectral : VelocitySpaceScheme
data OperatorSplit : Set where strang godunov : OperatorSplit
record ViriatoNumericalArchitecture : Set where constructor viriato-numerical-architecture; field solvedModels : List PlasmaModel; splitOptions : List OperatorSplit; parallelOptions : List ParallelScheme; perpendicularScheme : PerpendicularScheme; velocitySpaceScheme : VelocitySpaceScheme; sourceReference : String
open ViriatoNumericalArchitecture public
canonicalViriatoArchitecture = viriato-numerical-architecture (KREHM ∷ KRMHD ∷ reducedMHDLimit ∷ []) (strang ∷ godunov ∷ []) (macCormack2 ∷ tvdRK3Upwind7 ∷ []) pseudoSpectral hermiteSpectral "Loureiro et al., CPC 206 (2016) 45-63, DOI 10.1016/j.cpc.2016.05.004; arXiv:1505.02649"
operatorSplittingReceipt : S.ScientificMechanismReceipt
operatorSplittingReceipt = S.scientific-mechanism-receipt "Viriato" "parallel and perpendicular dynamics are separated numerically using Strang or Godunov operator splitting under a strong-guide-field reduced model" S.numericalMethod S.sourceBacked "Loureiro et al. 2016" "Numerical splitting is not a claim that the physical plasma literally evolves in separated stages."
hermiteReceipt : S.ScientificMechanismReceipt
hermiteReceipt = S.scientific-mechanism-receipt "Viriato" "parallel velocity-space dependence is represented spectrally using Hermite modes" S.numericalMethod S.sourceBacked "Loureiro et al. 2016" "Convergence depends on sufficient velocity-space resolution and closure/dissipation choices."
benchmarkReceipt : S.ScientificMechanismReceipt
benchmarkReceipt = S.scientific-mechanism-receipt "Viriato" "linear and nonlinear benchmarks include 2D and 3D Orszag-Tang-type decaying turbulence in fluid and kinetic regimes" S.benchmarkOrValidationTest S.sourceBacked "Loureiro et al. 2016" "Benchmark agreement validates selected equations/implementation tests, not every physical approximation for all plasmas."
reducedModelBoundary : S.ScientificMechanismReceipt
reducedModelBoundary = S.scientific-mechanism-receipt "KREHM/KRMHD" "Viriato solves reduced strongly magnetised plasma models applicable to turbulence and reconnection in their asymptotic regimes" S.constitutiveOrEngineeringMechanism S.sourceBacked "Loureiro et al. 2016" "Numerical accuracy does not remove reduced-model form error outside the derivation regime."
viriatoNeedsModelRegimeReceipt : S.ScientificReverseObligation
viriatoNeedsModelRegimeReceipt = S.scientific-reverse-obligation "application of Viriato to a physical plasma" S.mechanismToObservationWeld "show target-plasma ordering assumptions and control relevant neglected physics" "physical applicability of a particular simulation" "universal plasma truth from code convergence or benchmark success"
record CurrentViriatoScienceAssessment : Set where constructor current-viriato-science-assessment; field modelsOwned : Bool; modelsOwnedIsTrue : modelsOwned ≡ true; numericalArchitectureOwned : Bool; numericalArchitectureOwnedIsTrue : numericalArchitectureOwned ≡ true; benchmarkSuiteOwned : Bool; benchmarkSuiteOwnedIsTrue : benchmarkSuiteOwned ≡ true; universalPhysicalValidityOwned : Bool; universalPhysicalValidityOwnedIsFalse : universalPhysicalValidityOwned ≡ false
canonicalCurrentViriatoScienceAssessment = current-viriato-science-assessment true refl true refl true refl false refl
