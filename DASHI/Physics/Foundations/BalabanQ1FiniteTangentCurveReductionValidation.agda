module DASHI.Physics.Foundations.BalabanQ1FiniteTangentCurveReductionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.BalabanQ1FiniteTangentCurveReductionExact as Cut

freePerComponentSourcePathEliminated :
  Cut.freePerComponentSourcePathIsPrimitive ≡ false
freePerComponentSourcePathEliminated = refl

exactPresentCutTangentReused :
  Cut.q1CurveUsesExactPresentCutFiniteTangent ≡ true
exactPresentCutTangentReused = refl

metricTangentConstructionNotSecondLeaf :
  Cut.independentMetricTangentConstructionRequired ≡ false
metricTangentConstructionNotSecondLeaf = refl

remainingLeafIsOneTangentCurveRealisation :
  Cut.remainingQ1LeafIsTangentCurveSourceSemantics ≡ true
remainingLeafIsOneTangentCurveRealisation = refl

cmp109GaugeBPathNotSilentlyMetricStressPath :
  Cut.cmp109GaugeBPathIsNotMetricStressCurveByNotation ≡ true
cmp109GaugeBPathNotSilentlyMetricStressPath = refl
