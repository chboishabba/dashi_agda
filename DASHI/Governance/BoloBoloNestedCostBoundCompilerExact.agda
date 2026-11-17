module DASHI.Governance.BoloBoloNestedCostBoundCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloRobustCostBoundsExact as Robust

------------------------------------------------------------------------
-- COMPONENTWISE -> TOTAL ROBUST BOUND COMPILER.
--
-- Empirical work will naturally bound bolo-, tega-, wider-interface,
-- delegation and unresolved-dependency overhead separately.  The robust
-- comparison theorem consumes a total federation-overhead interval.  This
-- owner proves that separately justified component upper bounds can be summed
-- into a valid total upper bound without identifying the components with one
-- another or assuming any omitted overhead is zero.
------------------------------------------------------------------------

record NestedComponentCostBounds
  (components : Comparison.NestedBoloCostComponents) : Set where
  constructor nestedComponentCostBounds
  field
    removedLower : Nat
    removedUpper : Nat
    overheadLower : Nat

    boloInterfaceUpper : Nat
    tegaInterfaceUpper : Nat
    widerInterfaceUpper : Nat
    delegationUpper : Nat
    unresolvedUpper : Nat

    removedLower≤Actual :
      removedLower ≤ Comparison.removedGlobalCost components
    actualRemoved≤Upper :
      Comparison.removedGlobalCost components ≤ removedUpper
    overheadLower≤Actual :
      overheadLower ≤ Comparison.nestedFederationOverhead components

    boloActual≤Upper :
      Comparison.boloInterfaceCost components ≤ boloInterfaceUpper
    tegaActual≤Upper :
      Comparison.tegaInterfaceCost components ≤ tegaInterfaceUpper
    widerActual≤Upper :
      Comparison.widerInterfaceCost components ≤ widerInterfaceUpper
    delegationActual≤Upper :
      Comparison.nestedDelegationCost components ≤ delegationUpper
    unresolvedActual≤Upper :
      Comparison.nestedUnresolvedDependencyCost components ≤ unresolvedUpper

open NestedComponentCostBounds public

nestedComponentOverheadUpper :
  ∀ {components} → NestedComponentCostBounds components → Nat
nestedComponentOverheadUpper bounds =
  boloInterfaceUpper bounds
  + tegaInterfaceUpper bounds
  + widerInterfaceUpper bounds
  + delegationUpper bounds
  + unresolvedUpper bounds

nestedComponentUpperBoundsTotal :
  ∀ {components} →
  (bounds : NestedComponentCostBounds components) →
  Comparison.nestedFederationOverhead components
  ≤ nestedComponentOverheadUpper bounds
nestedComponentUpperBoundsTotal bounds =
  +-mono-≤
    (+-mono-≤
      (+-mono-≤
        (+-mono-≤
          (boloActual≤Upper bounds)
          (tegaActual≤Upper bounds))
        (widerActual≤Upper bounds))
      (delegationActual≤Upper bounds))
    (unresolvedActual≤Upper bounds)

compileNestedComponentBounds :
  ∀ {components} →
  (bounds : NestedComponentCostBounds components) →
  Robust.CostIntervalBounds (Comparison.nestedBoloCostModel components)
compileNestedComponentBounds bounds =
  Robust.costIntervalBounds
    (removedLower bounds)
    (removedUpper bounds)
    (overheadLower bounds)
    (nestedComponentOverheadUpper bounds)
    (removedLower≤Actual bounds)
    (actualRemoved≤Upper bounds)
    (overheadLower≤Actual bounds)
    (nestedComponentUpperBoundsTotal bounds)

record NestedComponentRobustWin
  {components : Comparison.NestedBoloCostComponents}
  (bounds : NestedComponentCostBounds components) : Set where
  constructor nestedComponentRobustWin
  field
    componentUpperBelowRemovedLower :
      nestedComponentOverheadUpper bounds < removedLower bounds

open NestedComponentRobustWin public

componentRobustWinCompiles :
  ∀ {components} →
  (bounds : NestedComponentCostBounds components) →
  NestedComponentRobustWin bounds →
  Robust.RobustWin (compileNestedComponentBounds bounds)
componentRobustWinCompiles bounds witness =
  Robust.robustWin (componentUpperBelowRemovedLower witness)

componentRobustWinImpliesStrictImprovement :
  ∀ {components} →
  (bounds : NestedComponentCostBounds components) →
  NestedComponentRobustWin bounds →
  Robust.StrictOrderImprovement (Comparison.nestedBoloCostModel components)
componentRobustWinImpliesStrictImprovement bounds witness =
  Robust.robustWinImpliesStrictOrderImprovement
    (compileNestedComponentBounds bounds)
    (componentRobustWinCompiles bounds witness)

------------------------------------------------------------------------
-- Tiny synthetic kernel exercise only; not empirical calibration.
------------------------------------------------------------------------

syntheticNestedBoundComponents : Comparison.NestedBoloCostComponents
syntheticNestedBoundComponents =
  Comparison.nestedBoloCostComponents 40 1 0 0 0 0 0

syntheticNestedBoundModel : Comparison.CounterfactualCoordinationCostModel
syntheticNestedBoundModel = Comparison.nestedBoloCostModel syntheticNestedBoundComponents

syntheticNestedComponentBounds : NestedComponentCostBounds syntheticNestedBoundComponents
syntheticNestedComponentBounds =
  nestedComponentCostBounds
    1 1 0
    0 0 0 0 0
    ≤-refl ≤-refl ≤-refl
    ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl

syntheticNestedComponentRobustWin :
  NestedComponentRobustWin syntheticNestedComponentBounds
syntheticNestedComponentRobustWin =
  nestedComponentRobustWin (s≤s z≤n)

syntheticNestedStrictImprovement :
  Robust.StrictOrderImprovement syntheticNestedBoundModel
syntheticNestedStrictImprovement =
  componentRobustWinImpliesStrictImprovement
    syntheticNestedComponentBounds
    syntheticNestedComponentRobustWin

------------------------------------------------------------------------
-- Attribution / interpretation boundary.
------------------------------------------------------------------------

record NestedCostBoundCompilerBoundary : Set where
  constructor nestedCostBoundCompilerBoundary
  field
    separateComponentBoundsMayCompileToTotalUpper : Bool
    omittedOverheadMayBeAssumedZero : Bool
    componentBoundsQuotedFromBoloBolo : Bool
    componentBoundsAutomaticallyIdentifiedFromOWSLexemes : Bool
    compiledUpperBoundCreatesPoliticalLegitimacy : Bool
    componentBoundsCreatePoliticalLegitimacy : Bool

open NestedCostBoundCompilerBoundary public

canonicalNestedCostBoundCompilerBoundary : NestedCostBoundCompilerBoundary
canonicalNestedCostBoundCompilerBoundary =
  nestedCostBoundCompilerBoundary true false false false false false

canonicalNestedCostBoundCompilerReceipt : GenericReceipt.GenericReceipt
canonicalNestedCostBoundCompilerReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo componentwise robust-cost-bound compiler"
    "DASHI.Governance.BoloBoloNestedCostBoundCompilerExact"
    "compileNestedComponentBounds / componentRobustWinImpliesStrictImprovement / canonicalNestedCostBoundCompilerBoundary"
    "proves that separately justified upper bounds for bolo-, tega-, wider-interface, delegation and unresolved-dependency overhead sum to a valid total federation-overhead upper bound consumable by the existing robust comparison theorem"
    "no omitted overhead is set to zero by the compiler; component bounds are DASHI evidence targets rather than p.m. claims, OWS lexical markers do not identify them, and a compiled coordination bound creates neither legitimacy nor broader political authority"
    "agda -i . DASHI/Governance/BoloBoloNestedCostBoundCompilerRegression.agda"
