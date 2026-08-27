module DASHI.Core.McCallCategoryStrategyBoundaryExact where

------------------------------------------------------------------------
-- MCCALL CATEGORY-STRATEGY BOUNDARY
--
-- SOURCE CALIBRATION
-- Leslie McCall, "The Complexity of Intersectionality", Signs 30(3),
-- 1771-1800 (2005). DOI 10.1086/426800.
--
-- McCall distinguishes anticategorical, intracategorical and intercategorical
-- methodological approaches. DASHI makes movement between them an explicit
-- translation obligation rather than treating "intersectionality" as one
-- undifferentiated method.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data CategoryStrategy : Set where
  anticategorical intracategorical intercategorical : CategoryStrategy

data FixedAxisModel : Set where fixedAxisModel : FixedAxisModel
data AnticategoricalConclusion : Set where categoryRefusalConclusion : AnticategoricalConclusion

data CategoryRechartWitness : CategoryStrategy → CategoryStrategy → Set where
  explicitInterToAntiRechart : CategoryRechartWitness intercategorical anticategorical

intercategoricalRectangleModel : CategoryStrategy
intercategoricalRectangleModel = intercategorical

noSilentInterToAnti :
  CategoryRechartWitness intercategorical anticategorical → ⊤
noSilentInterToAnti explicitInterToAntiRechart = tt

record CategoryStrategyBoundary : Set where
  constructor category-strategy-boundary
  field
    intercategoricalModelAutomaticallyYieldsAnticategoricalConclusion : Bool
    intercategoricalModelAutomaticallyYieldsAnticategoricalConclusionIsFalse :
      intercategoricalModelAutomaticallyYieldsAnticategoricalConclusion ≡ false
    allIntersectionalMethodsUseFixedAxes : Bool
    allIntersectionalMethodsUseFixedAxesIsFalse : allIntersectionalMethodsUseFixedAxes ≡ false
    strategyTranslationRequiresExplicitWitness : Bool
    strategyTranslationRequiresExplicitWitnessIsTrue :
      strategyTranslationRequiresExplicitWitness ≡ true

canonicalCategoryStrategyBoundary : CategoryStrategyBoundary
canonicalCategoryStrategyBoundary = category-strategy-boundary false refl false refl true refl
