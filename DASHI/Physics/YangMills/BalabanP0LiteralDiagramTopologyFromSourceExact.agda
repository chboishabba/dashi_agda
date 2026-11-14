module DASHI.Physics.YangMills.BalabanP0LiteralDiagramTopologyFromSourceExact where

-- Concrete original four-diagram AST constructor, NOT an invented
-- physical momentum vertex or an independently sampled quadrature.
-- Existing Wilson/FP/Haar modules provide rich physical jets and color
-- coefficients, but do not yet prove the indexed Fourier numerator
-- expressions used at this single mixed external-momentum two-jet.
-- Therefore the four numerators are explicit SAME-SOURCE inputs.
--
-- Paid here:
--   (i) canonical original convention;
--   (ii) bubble and ghost propagator pair D(p)D(p+k);
--   (iii) gauge tadpole D(p); Haar contact denominator 1;
--   (iv) full original LiteralDiagramExpressions inhabitant with all
--        four DiagramExpression quotient definitions by refl;
--   (v) exact identification of these denominator ASTs.
--
-- Remaining: physically derive these numerator expressions from actual
-- Wilson 3/4-vertices, background FP operator and Haar Casimir/chart.
-- In particular, the source parser lacks indexed Lorentz contractions;
-- arbitrary numeral placeholders are not physical proof receipts.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact as Convention

loopPropagatorDenominator : Eval.DiagramExpression
loopPropagatorDenominator =
  Eval.atom (Eval.hatMomentumSquared Eval.loopMomentum)

shiftedPropagatorDenominator : Eval.DiagramExpression
shiftedPropagatorDenominator =
  Eval.atom (Eval.hatMomentumSquared Eval.shiftedMomentum)

pairedPropagatorDenominator : Eval.DiagramExpression
pairedPropagatorDenominator =
  Eval.multiply loopPropagatorDenominator shiftedPropagatorDenominator

haarContactDenominator : Eval.DiagramExpression
haarContactDenominator = Eval.rationalConstant 1ℚ

record ActualPhysicalDiagramNumeratorSources : Set where
  field
    -- MUST be source-derived and carry physical provenance externally.
    -- No Set-valued fake vertex validity is constructed here.
    sourceWilsonQuadraticVertex : Eval.DiagramExpression
    sourceWilsonCubicVertex : Eval.DiagramExpression
    sourceWilsonQuarticVertex : Eval.DiagramExpression
    sourceBackgroundFaddeevPopovOperator : Eval.DiagramExpression
    sourceGhostBackgroundVertex : Eval.DiagramExpression
    sourceHaarQuadraticVertex : Eval.DiagramExpression

    -- The signed numerator convention is already included in the
    -- physical source's ghost contraction: no second minus is inserted.
    sourceGaugeBubbleNumerator : Eval.DiagramExpression
    sourceGaugeTadpoleNumerator : Eval.DiagramExpression
    sourceSignedGhostLoopNumerator : Eval.DiagramExpression
    sourceHaarContactNumerator : Eval.DiagramExpression
open ActualPhysicalDiagramNumeratorSources public

literalPhysicalTopology :
  ActualPhysicalDiagramNumeratorSources →
  Eval.LiteralDiagramExpressions
literalPhysicalTopology source = record
  { Eval.LiteralDiagramExpressions.convention =
      Convention.canonicalWilsonOneLoopConvention
  ; Eval.LiteralDiagramExpressions.conventionIsCanonical = refl
  ; Eval.LiteralDiagramExpressions.wilsonQuadraticVertex =
      sourceWilsonQuadraticVertex source
  ; Eval.LiteralDiagramExpressions.wilsonCubicVertex =
      sourceWilsonCubicVertex source
  ; Eval.LiteralDiagramExpressions.wilsonQuarticVertex =
      sourceWilsonQuarticVertex source
  ; Eval.LiteralDiagramExpressions.faddeevPopovOperator =
      sourceBackgroundFaddeevPopovOperator source
  ; Eval.LiteralDiagramExpressions.ghostBackgroundVertex =
      sourceGhostBackgroundVertex source
  ; Eval.LiteralDiagramExpressions.haarQuadraticVertex =
      sourceHaarQuadraticVertex source
  ; Eval.LiteralDiagramExpressions.gaugeBubbleNumerator =
      sourceGaugeBubbleNumerator source
  ; Eval.LiteralDiagramExpressions.gaugeBubbleDenominator =
      pairedPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.gaugeTadpoleNumerator =
      sourceGaugeTadpoleNumerator source
  ; Eval.LiteralDiagramExpressions.gaugeTadpoleDenominator =
      loopPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.ghostLoopNumerator =
      sourceSignedGhostLoopNumerator source
  ; Eval.LiteralDiagramExpressions.ghostLoopDenominator =
      pairedPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.haarLoopNumerator =
      sourceHaarContactNumerator source
  ; Eval.LiteralDiagramExpressions.haarLoopDenominator =
      haarContactDenominator
  ; Eval.LiteralDiagramExpressions.gaugeBubble =
      Eval.divide (sourceGaugeBubbleNumerator source)
        pairedPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.gaugeTadpole =
      Eval.divide (sourceGaugeTadpoleNumerator source)
        loopPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.ghostLoop =
      Eval.divide (sourceSignedGhostLoopNumerator source)
        pairedPropagatorDenominator
  ; Eval.LiteralDiagramExpressions.haarLoop =
      Eval.divide (sourceHaarContactNumerator source)
        haarContactDenominator
  ; Eval.LiteralDiagramExpressions.gaugeBubbleDefinition = refl
  ; Eval.LiteralDiagramExpressions.gaugeTadpoleDefinition = refl
  ; Eval.LiteralDiagramExpressions.ghostLoopDefinition = refl
  ; Eval.LiteralDiagramExpressions.haarLoopDefinition = refl
  }

literalBubbleDenominatorIsPaired :
  ∀ source →
  Eval.gaugeBubbleDenominator (literalPhysicalTopology source)
    ≡ pairedPropagatorDenominator
literalBubbleDenominatorIsPaired source = refl

literalGhostDenominatorIsSamePaired :
  ∀ source →
  Eval.ghostLoopDenominator (literalPhysicalTopology source)
    ≡ Eval.gaugeBubbleDenominator (literalPhysicalTopology source)
literalGhostDenominatorIsSamePaired source = refl

literalTadpoleDenominatorIsLoop :
  ∀ source →
  Eval.gaugeTadpoleDenominator (literalPhysicalTopology source)
    ≡ loopPropagatorDenominator
literalTadpoleDenominatorIsLoop source = refl

literalHaarDenominatorIsOne :
  ∀ source →
  Eval.haarLoopDenominator (literalPhysicalTopology source)
    ≡ Eval.rationalConstant 1ℚ
literalHaarDenominatorIsOne source = refl

-- The Ward identity is NOT implied by the above definitional
-- equalities. For example an arbitrary ghost numerator could be
-- replaced by any DiagramExpression and retain the same denominator.
-- All numerical source insertions must be checked against physical
-- indexed Wilson/FP/Haar vertex contractions before P0.4/P0.5 claim.
