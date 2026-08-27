module DASHI.Governance.ONeill2018MethodsBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.SafeJustSourceRegistryExact as Sources
import DASHI.Governance.SafeJustIndicatorSystemExact as Indicators

------------------------------------------------------------------------
-- O'NEILL ET AL. 2018 METHODS BOUNDARY
--
-- The article fits every 7 x 11 biophysical/social pair with three OLS curve
-- families.  The equations are retained as provenance-bearing model syntax;
-- fitted association is deliberately not retyped as a causal production law.
------------------------------------------------------------------------

data FitFamily : Set where
  linearFit linearLogFit saturationFit : FitFamily

fitEquation : FitFamily → String
fitEquation linearFit = "y = a1 + b1 x"
fitEquation linearLogFit = "y = a2 + b2 log(x)"
fitEquation saturationFit = "log(y_sat - y) = a3 + b3 log(x)"

saturationConvention : String
saturationConvention = "y_sat = 1.1 * max(y)"

biophysicalCoordinateCount : Nat
biophysicalCoordinateCount = 7

socialCoordinateCount : Nat
socialCoordinateCount = 11

pairCount : Nat
pairCount = biophysicalCoordinateCount * socialCoordinateCount

curveCount : Nat
curveCount = 3

regressionTestCount : Nat
regressionTestCount = pairCount * curveCount

pairCountIs77 : pairCount ≡ 77
pairCountIs77 = refl

regressionTestCountIs231 : regressionTestCount ≡ 231
regressionTestCountIs231 = refl

record RegressionProtocol : Set where
  constructor regressionProtocol
  field
    estimator : String
    significanceAlpha : String
    testedFamilies : Nat
    repeatedTests : Nat
    saturationRule : String

canonicalProtocol : RegressionProtocol
canonicalProtocol = regressionProtocol
  "ordinary least squares (OLS)"
  "0.01"
  curveCount
  regressionTestCount
  saturationConvention

------------------------------------------------------------------------
-- Claim authority: observed-country result != universal impossibility.
------------------------------------------------------------------------

data ClaimScope : Set where
  observedDataset universalSocietySpace : ClaimScope

data ClaimKind : Set where
  noObservedCountrySafeAndJust universalSafeAndJustImpossible : ClaimKind

record EmpiricalClaim : Set where
  constructor empiricalClaim
  field
    scope : ClaimScope
    kind : ClaimKind
    source : Sources.SourceReference

paperObservedClaim : EmpiricalClaim
paperObservedClaim = empiricalClaim observedDataset noObservedCountrySafeAndJust Sources.oneill2018

data UniversalImpossibilityCertificate : Set where

paperDoesNotSupplyUniversalImpossibility : UniversalImpossibilityCertificate → ⊥
paperDoesNotSupplyUniversalImpossibility ()

------------------------------------------------------------------------
-- Statistical association / model-family boundaries.
------------------------------------------------------------------------

data CausalResourceProductionLaw : Set where

data ModelSelectionImpliesCausalMechanism : Set where

olsAssociationDoesNotSupplyCausalLaw : CausalResourceProductionLaw → ⊥
olsAssociationDoesNotSupplyCausalLaw ()

bestFitDoesNotIdentifyMechanism : ModelSelectionImpliesCausalMechanism → ⊥
bestFitDoesNotIdentifyMechanism ()

record MethodsBoundary : Set where
  constructor methodsBoundary
  field
    sevenByElevenMeansSeventySevenPairs : Bool
    sevenByElevenMeansSeventySevenPairsIsTrue :
      sevenByElevenMeansSeventySevenPairs ≡ true
    threeFitsPerPairMeansTwoHundredThirtyOneTests : Bool
    threeFitsPerPairMeansTwoHundredThirtyOneTestsIsTrue :
      threeFitsPerPairMeansTwoHundredThirtyOneTests ≡ true
    crossNationalOLSAssociationIsCausalProductionFunction : Bool
    crossNationalOLSAssociationIsCausalProductionFunctionIsFalse :
      crossNationalOLSAssociationIsCausalProductionFunction ≡ false
    noObservedSafeAndJustCountryMeansUniversalImpossibility : Bool
    noObservedSafeAndJustCountryMeansUniversalImpossibilityIsFalse :
      noObservedSafeAndJustCountryMeansUniversalImpossibility ≡ false

canonicalMethodsBoundary : MethodsBoundary
canonicalMethodsBoundary = methodsBoundary true refl true refl false refl false refl
