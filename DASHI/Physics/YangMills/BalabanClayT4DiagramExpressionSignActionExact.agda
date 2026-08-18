module DASHI.Physics.YangMills.BalabanClayT4DiagramExpressionSignActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223. Section 5, equations (5.6)--(5.8).
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Put the actual one-loop DiagramExpression AST under the reflection subgroup
-- (C2)^4 used by the generated Brillouin action. Sine-half atoms are odd in a
-- reflected coordinate; cosine atoms and hat-momentum squares are even when
-- loop and external momentum are transformed jointly. The action is lifted
-- recursively through the expression tree, with exact rational semantics and
-- the commuting square
--
--   eval env (epsilon . expression)
--     = eval (epsilon . env) expression.
--
-- Thus the Walsh reduction attaches to literal diagram syntax rather than to
-- an unrelated scalar receipt once Wilson/FP/Haar expressions are instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; -_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as AST

axisSlot : AST.AxisIndex → Cube.BondSlot4
axisSlot AST.axis0 = Cube.slot0
axisSlot AST.axis1 = Cube.slot1
axisSlot AST.axis2 = Cube.slot2
axisSlot AST.axis3 = Cube.slot3

maskFlipsAxis : Cube.Subset4 → AST.AxisIndex → Agda.Builtin.Bool.Bool
maskFlipsAxis mask axis = Cube.contains (axisSlot axis) mask

negateIfFlipped :
  Cube.Subset4 → AST.AxisIndex → AST.DiagramExpression → AST.DiagramExpression
negateIfFlipped mask axis expression with maskFlipsAxis mask axis
... | Agda.Builtin.Bool.false = expression
... | Agda.Builtin.Bool.true = AST.negate expression

signActAtom : Cube.Subset4 → AST.TrigAtom → AST.DiagramExpression
signActAtom mask (AST.sineHalf role axis) =
  negateIfFlipped mask axis (AST.atom (AST.sineHalf role axis))
signActAtom mask (AST.cosineFull role axis) =
  AST.atom (AST.cosineFull role axis)
signActAtom mask (AST.hatMomentumSquared role) =
  AST.atom (AST.hatMomentumSquared role)
signActAtom mask AST.colorCasimir = AST.atom AST.colorCasimir
signActAtom mask AST.gaugeParameter = AST.atom AST.gaugeParameter

signActExpression : Cube.Subset4 → AST.DiagramExpression → AST.DiagramExpression
signActExpression mask (AST.rationalConstant value) = AST.rationalConstant value
signActExpression mask (AST.atom trigAtom) = signActAtom mask trigAtom
signActExpression mask (AST.add left right) =
  AST.add (signActExpression mask left) (signActExpression mask right)
signActExpression mask (AST.subtract left right) =
  AST.subtract (signActExpression mask left) (signActExpression mask right)
signActExpression mask (AST.multiply left right) =
  AST.multiply (signActExpression mask left) (signActExpression mask right)
signActExpression mask (AST.divide numerator denominator) =
  AST.divide (signActExpression mask numerator) (signActExpression mask denominator)
signActExpression mask (AST.negate expression) =
  AST.negate (signActExpression mask expression)

ExactTrigEnvironment : Set
ExactTrigEnvironment = AST.TrigAtom → ℚ

transformEnvironment :
  Cube.Subset4 → ExactTrigEnvironment → ExactTrigEnvironment
transformEnvironment mask environment (AST.sineHalf role axis)
  with maskFlipsAxis mask axis
... | Agda.Builtin.Bool.false = environment (AST.sineHalf role axis)
... | Agda.Builtin.Bool.true = - environment (AST.sineHalf role axis)
transformEnvironment mask environment (AST.cosineFull role axis) =
  environment (AST.cosineFull role axis)
transformEnvironment mask environment (AST.hatMomentumSquared role) =
  environment (AST.hatMomentumSquared role)
transformEnvironment mask environment AST.colorCasimir = environment AST.colorCasimir
transformEnvironment mask environment AST.gaugeParameter = environment AST.gaugeParameter

evaluateExact : ExactTrigEnvironment → AST.DiagramExpression → ℚ
evaluateExact environment (AST.rationalConstant value) = value
evaluateExact environment (AST.atom trigAtom) = environment trigAtom
evaluateExact environment (AST.add left right) =
  evaluateExact environment left + evaluateExact environment right
evaluateExact environment (AST.subtract left right) =
  evaluateExact environment left - evaluateExact environment right
evaluateExact environment (AST.multiply left right) =
  evaluateExact environment left * evaluateExact environment right
evaluateExact environment (AST.divide numerator denominator) =
  evaluateExact environment numerator / evaluateExact environment denominator
evaluateExact environment (AST.negate expression) = - evaluateExact environment expression

signActAtomSemantics :
  (mask : Cube.Subset4) →
  (environment : ExactTrigEnvironment) →
  (trigAtom : AST.TrigAtom) →
  evaluateExact environment (signActAtom mask trigAtom)
  ≡ transformEnvironment mask environment trigAtom
signActAtomSemantics mask environment (AST.sineHalf role axis)
  with maskFlipsAxis mask axis
... | Agda.Builtin.Bool.false = refl
... | Agda.Builtin.Bool.true = refl
signActAtomSemantics mask environment (AST.cosineFull role axis) = refl
signActAtomSemantics mask environment (AST.hatMomentumSquared role) = refl
signActAtomSemantics mask environment AST.colorCasimir = refl
signActAtomSemantics mask environment AST.gaugeParameter = refl

signActionEvaluationCommutes :
  (mask : Cube.Subset4) →
  (environment : ExactTrigEnvironment) →
  (expression : AST.DiagramExpression) →
  evaluateExact environment (signActExpression mask expression)
  ≡ evaluateExact (transformEnvironment mask environment) expression
signActionEvaluationCommutes mask environment (AST.rationalConstant value) = refl
signActionEvaluationCommutes mask environment (AST.atom trigAtom) =
  signActAtomSemantics mask environment trigAtom
signActionEvaluationCommutes mask environment (AST.add left right) =
  cong₂ _+_
    (signActionEvaluationCommutes mask environment left)
    (signActionEvaluationCommutes mask environment right)
signActionEvaluationCommutes mask environment (AST.subtract left right) =
  cong₂ _-_
    (signActionEvaluationCommutes mask environment left)
    (signActionEvaluationCommutes mask environment right)
signActionEvaluationCommutes mask environment (AST.multiply left right) =
  cong₂ _*_
    (signActionEvaluationCommutes mask environment left)
    (signActionEvaluationCommutes mask environment right)
signActionEvaluationCommutes mask environment (AST.divide numerator denominator) =
  cong₂ _/_
    (signActionEvaluationCommutes mask environment numerator)
    (signActionEvaluationCommutes mask environment denominator)
signActionEvaluationCommutes mask environment (AST.negate expression) =
  cong -_ (signActionEvaluationCommutes mask environment expression)

emptySignActAtom :
  (trigAtom : AST.TrigAtom) →
  signActAtom Cube.empty trigAtom ≡ AST.atom trigAtom
emptySignActAtom (AST.sineHalf role AST.axis0) = refl
emptySignActAtom (AST.sineHalf role AST.axis1) = refl
emptySignActAtom (AST.sineHalf role AST.axis2) = refl
emptySignActAtom (AST.sineHalf role AST.axis3) = refl
emptySignActAtom (AST.cosineFull role axis) = refl
emptySignActAtom (AST.hatMomentumSquared role) = refl
emptySignActAtom AST.colorCasimir = refl
emptySignActAtom AST.gaugeParameter = refl

emptySignActionIdentity :
  (expression : AST.DiagramExpression) →
  signActExpression Cube.empty expression ≡ expression
emptySignActionIdentity (AST.rationalConstant value) = refl
emptySignActionIdentity (AST.atom trigAtom) = emptySignActAtom trigAtom
emptySignActionIdentity (AST.add left right) =
  cong₂ AST.add (emptySignActionIdentity left) (emptySignActionIdentity right)
emptySignActionIdentity (AST.subtract left right) =
  cong₂ AST.subtract (emptySignActionIdentity left) (emptySignActionIdentity right)
emptySignActionIdentity (AST.multiply left right) =
  cong₂ AST.multiply (emptySignActionIdentity left) (emptySignActionIdentity right)
emptySignActionIdentity (AST.divide numerator denominator) =
  cong₂ AST.divide
    (emptySignActionIdentity numerator)
    (emptySignActionIdentity denominator)
emptySignActionIdentity (AST.negate expression) =
  cong AST.negate (emptySignActionIdentity expression)

diagramExpressionSignActionLevel : ProofLevel
diagramExpressionSignActionLevel = machineChecked

diagramExpressionSignSemanticsLevel : ProofLevel
diagramExpressionSignSemanticsLevel = machineChecked
