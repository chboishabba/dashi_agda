module DASHI.Physics.YangMills.BalabanClayT4OriginalEvaluatorFourOrbitEndpointSumsExact where

-- SAME-SOURCE EXACT ENDPOINT QUADRATURE FOLD.
-- No arbitrary rational four-cell contributions are inserted:
-- lower/upper endpoints come from the ORIGINAL recursive evaluator
-- at the ORIGINAL LiteralScalarIntegrandExpression.regularIntegrand.
-- The 240 -> 4 identities require the existing seven semantic
-- generator certificates; they are not fabricated here.
--
-- Geometric four-orbit normalized weights 4,6,4,1 are exact.
-- This is NOT a numerical certification of the four physical integrals.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact as Four
import DASHI.Physics.YangMills.BalabanClayT4LiteralSemanticSevenGeneratorTransportExact as Semantic
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Sym
import DASHI.Physics.YangMills.BalabanCMP109FourOrbitNormalizedQuadratureExact as FourSum

sourceLower :
  ∀ {expressions ward scalarData} →
  Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Grid.GridCell4 → ℚ
sourceLower {scalarData = scalarData} source cell =
  Eval.lower
    (Eval.evaluateExpression (Eval.arithmetic source)
      (Eval.environment source cell)
      (Eval.regularIntegrand scalarData))

sourceUpper :
  ∀ {expressions ward scalarData} →
  Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Grid.GridCell4 → ℚ
sourceUpper {scalarData = scalarData} source cell =
  Eval.upper
    (Eval.evaluateExpression (Eval.arithmetic source)
      (Eval.environment source cell)
      (Eval.regularIntegrand scalarData))

-- Source receipt identity, not a synthetic new per-box constant.
sourceLowerIsOriginalReceipt :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    cell →
  Eval.lower
    (Eval.intervalValue
      (Eval.regularIntegrandEvaluation source cell))
  ≡ sourceLower source cell
sourceLowerIsOriginalReceipt source cell =
  cong Eval.lower
    (Eval.intervalValueExact
      (Eval.regularIntegrandEvaluation source cell))

sourceUpperIsOriginalReceipt :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    cell →
  Eval.upper
    (Eval.intervalValue
      (Eval.regularIntegrandEvaluation source cell))
  ≡ sourceUpper source cell
sourceUpperIsOriginalReceipt source cell =
  cong Eval.upper
    (Eval.intervalValueExact
      (Eval.regularIntegrandEvaluation source cell))

sourceLowerGenerator :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
    ∀ generator cell →
    sourceLower source cell ≡
      sourceLower source (Action.act generator cell)
sourceLowerGenerator source semantic generator cell
  rewrite Semantic.canonicalActionIsOrbitAction generator cell =
  cong Eval.lower
    (sym (Semantic.originalLiteralSemanticOneGeneratorTransport
      semantic (Four.asOrbitGenerator generator) cell))

sourceUpperGenerator :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
    ∀ generator cell →
    sourceUpper source cell ≡
      sourceUpper source (Action.act generator cell)
sourceUpperGenerator source semantic generator cell
  rewrite Semantic.canonicalActionIsOrbitAction generator cell =
  cong Eval.upper
    (sym (Semantic.originalLiteralSemanticOneGeneratorTransport
      semantic (Four.asOrbitGenerator generator) cell))

sourceLowerInvariant :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
  Action.GeneratorInvariantRationalContribution (sourceLower source)
sourceLowerInvariant source semantic = record
  { Action.generatorInvariant = sourceLowerGenerator source semantic }

sourceUpperInvariant :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
  Action.GeneratorInvariantRationalContribution (sourceUpper source)
sourceUpperInvariant source semantic = record
  { Action.generatorInvariant = sourceUpperGenerator source semantic }

-- Convert the original semantic invariance to the existing CMP109
-- rational-scalar symmetry API ONLY AFTER it has been proved for the
-- actual selected evaluator via the seven generator witnesses.
asSourceScalarSymmetry :
  ∀ {contribution} →
  Action.GeneratorInvariantRationalContribution contribution →
  Sym.CMP109ScalarEuclideanSymmetry contribution
asSourceScalarSymmetry invariant = record
  { Sym.reflectionInvariant = λ axis cell →
      Action.generatorInvariant invariant
        (Sym.reflectionGenerator axis) cell
  ; Sym.permutationInvariant = λ permutation cell →
      Action.generatorInvariant invariant
        (Sym.permutationGenerator permutation) cell
  }

actualLowerEndpointNormalized240ToFour :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
  FourSum.normalizedRegularSum (sourceLower source)
    ≡ FourSum.fourOrbitNormalizedValue (sourceLower source)
actualLowerEndpointNormalized240ToFour source semantic =
  FourSum.sourceSymmetryNormalizedQuadrature
    (asSourceScalarSymmetry (sourceLowerInvariant source semantic))

actualUpperEndpointNormalized240ToFour :
  ∀ {expressions ward scalarData}
    (source : Eval.LiteralGeneratedBoxEvaluator expressions ward scalarData)
    (semantic : Semantic.LiteralSevenSemanticGeneratorData
      scalarData (Eval.arithmetic source) (Eval.environment source)) →
  FourSum.normalizedRegularSum (sourceUpper source)
    ≡ FourSum.fourOrbitNormalizedValue (sourceUpper source)
actualUpperEndpointNormalized240ToFour source semantic =
  FourSum.sourceSymmetryNormalizedQuadrature
    (asSourceScalarSymmetry (sourceUpperInvariant source semantic))

-- The actual source Eval.CertifiedBoxQuadrature fields additionally
-- contain hessianBoundValid, quadratureErrorFormulaValid and
-- trueIntegralInsideIntervalPlusError, each of type Set.
-- No term here inhabits them or manufactures a physical scalar integral.
