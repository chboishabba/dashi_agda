module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Ludwig D. Faddeev and Victor N. Popov,
-- "Feynman Diagrams for the Yang--Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Define the signed-permutation action on the ACTUAL DiagramExpression syntax
-- used by the 240-box Wilson/ghost/Haar evaluator.  The action is JOINT in the
-- momentum role: loop, external and shifted momenta all transform on the same
-- selected coordinate.  Consequently sine-half atoms are odd, cosine atoms are
-- even, and hat-momentum-squared atoms are scalar invariants.
--
-- This file intentionally stops one semantic step before asserting that the
-- source regularIntegrand is invariant: LiteralScalarIntegrandExpression still
-- stores that expression abstractly.  The finite syntax/action theorem is now
-- complete; identifying the source expression with an invariant syntax tree is
-- the remaining literal Wilson/ghost/Haar source calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit

axisAction : Orbit.HyperoctahedralGenerator → Eval.AxisIndex → Eval.AxisIndex
axisAction Orbit.identity axis = axis
axisAction Orbit.flip0 axis = axis
axisAction Orbit.flip1 axis = axis
axisAction Orbit.flip2 axis = axis
axisAction Orbit.flip3 axis = axis
axisAction Orbit.swap01 Eval.axis0 = Eval.axis1
axisAction Orbit.swap01 Eval.axis1 = Eval.axis0
axisAction Orbit.swap01 Eval.axis2 = Eval.axis2
axisAction Orbit.swap01 Eval.axis3 = Eval.axis3
axisAction Orbit.swap12 Eval.axis0 = Eval.axis0
axisAction Orbit.swap12 Eval.axis1 = Eval.axis2
axisAction Orbit.swap12 Eval.axis2 = Eval.axis1
axisAction Orbit.swap12 Eval.axis3 = Eval.axis3
axisAction Orbit.swap23 Eval.axis0 = Eval.axis0
axisAction Orbit.swap23 Eval.axis1 = Eval.axis1
axisAction Orbit.swap23 Eval.axis2 = Eval.axis3
axisAction Orbit.swap23 Eval.axis3 = Eval.axis2

flipsAxis : Orbit.HyperoctahedralGenerator → Eval.AxisIndex → Bool
flipsAxis Orbit.flip0 Eval.axis0 = true
flipsAxis Orbit.flip1 Eval.axis1 = true
flipsAxis Orbit.flip2 Eval.axis2 = true
flipsAxis Orbit.flip3 Eval.axis3 = true
flipsAxis _ _ = false

transformAtom : Orbit.HyperoctahedralGenerator → Eval.TrigAtom → Eval.DiagramExpression
transformAtom generator (Eval.sineHalf role axis) with flipsAxis generator axis
... | true = Eval.negate (Eval.atom (Eval.sineHalf role (axisAction generator axis)))
... | false = Eval.atom (Eval.sineHalf role (axisAction generator axis))
transformAtom generator (Eval.cosineFull role axis) =
  Eval.atom (Eval.cosineFull role (axisAction generator axis))
transformAtom generator (Eval.hatMomentumSquared role) =
  Eval.atom (Eval.hatMomentumSquared role)
transformAtom generator Eval.colorCasimir = Eval.atom Eval.colorCasimir
transformAtom generator Eval.gaugeParameter = Eval.atom Eval.gaugeParameter

transformExpression : Orbit.HyperoctahedralGenerator → Eval.DiagramExpression → Eval.DiagramExpression
transformExpression generator (Eval.rationalConstant value) = Eval.rationalConstant value
transformExpression generator (Eval.atom atom) = transformAtom generator atom
transformExpression generator (Eval.add left right) =
  Eval.add (transformExpression generator left) (transformExpression generator right)
transformExpression generator (Eval.subtract left right) =
  Eval.subtract (transformExpression generator left) (transformExpression generator right)
transformExpression generator (Eval.multiply left right) =
  Eval.multiply (transformExpression generator left) (transformExpression generator right)
transformExpression generator (Eval.divide left right) =
  Eval.divide (transformExpression generator left) (transformExpression generator right)
transformExpression generator (Eval.negate value) =
  Eval.negate (transformExpression generator value)

hatMomentumSquaredJointScalarExact : ∀ generator role →
  transformExpression generator (Eval.atom (Eval.hatMomentumSquared role))
  ≡ Eval.atom (Eval.hatMomentumSquared role)
hatMomentumSquaredJointScalarExact generator role = refl

cosineJointEvenUnderFlip0 : ∀ role →
  transformExpression Orbit.flip0 (Eval.atom (Eval.cosineFull role Eval.axis0))
  ≡ Eval.atom (Eval.cosineFull role Eval.axis0)
cosineJointEvenUnderFlip0 role = refl

cosineJointEvenUnderFlip1 : ∀ role →
  transformExpression Orbit.flip1 (Eval.atom (Eval.cosineFull role Eval.axis1))
  ≡ Eval.atom (Eval.cosineFull role Eval.axis1)
cosineJointEvenUnderFlip1 role = refl

cosineJointEvenUnderFlip2 : ∀ role →
  transformExpression Orbit.flip2 (Eval.atom (Eval.cosineFull role Eval.axis2))
  ≡ Eval.atom (Eval.cosineFull role Eval.axis2)
cosineJointEvenUnderFlip2 role = refl

cosineJointEvenUnderFlip3 : ∀ role →
  transformExpression Orbit.flip3 (Eval.atom (Eval.cosineFull role Eval.axis3))
  ≡ Eval.atom (Eval.cosineFull role Eval.axis3)
cosineJointEvenUnderFlip3 role = refl

sineJointOddUnderFlip0 : ∀ role →
  transformExpression Orbit.flip0 (Eval.atom (Eval.sineHalf role Eval.axis0))
  ≡ Eval.negate (Eval.atom (Eval.sineHalf role Eval.axis0))
sineJointOddUnderFlip0 role = refl

sineJointOddUnderFlip1 : ∀ role →
  transformExpression Orbit.flip1 (Eval.atom (Eval.sineHalf role Eval.axis1))
  ≡ Eval.negate (Eval.atom (Eval.sineHalf role Eval.axis1))
sineJointOddUnderFlip1 role = refl

sineJointOddUnderFlip2 : ∀ role →
  transformExpression Orbit.flip2 (Eval.atom (Eval.sineHalf role Eval.axis2))
  ≡ Eval.negate (Eval.atom (Eval.sineHalf role Eval.axis2))
sineJointOddUnderFlip2 role = refl

sineJointOddUnderFlip3 : ∀ role →
  transformExpression Orbit.flip3 (Eval.atom (Eval.sineHalf role Eval.axis3))
  ≡ Eval.negate (Eval.atom (Eval.sineHalf role Eval.axis3))
sineJointOddUnderFlip3 role = refl

axisPermutationRenamesCosine01 : ∀ role →
  transformExpression Orbit.swap01 (Eval.atom (Eval.cosineFull role Eval.axis0))
  ≡ Eval.atom (Eval.cosineFull role Eval.axis1)
axisPermutationRenamesCosine01 role = refl

axisPermutationRenamesSine01 : ∀ role →
  transformExpression Orbit.swap01 (Eval.atom (Eval.sineHalf role Eval.axis0))
  ≡ Eval.atom (Eval.sineHalf role Eval.axis1)
axisPermutationRenamesSine01 role = refl

record JointMomentumInvariantExpression (expression : Eval.DiagramExpression) : Set where
  field
    invariantGenerator : ∀ generator → transformExpression generator expression ≡ expression
open JointMomentumInvariantExpression public

record FixedAxisInvariantExpression (expression : Eval.DiagramExpression) : Set where
  field
    transverseSwap12 : transformExpression Orbit.swap12 expression ≡ expression
    transverseSwap23 : transformExpression Orbit.swap23 expression ≡ expression
    sign0 : transformExpression Orbit.flip0 expression ≡ expression
    sign1 : transformExpression Orbit.flip1 expression ≡ expression
    sign2 : transformExpression Orbit.flip2 expression ≡ expression
    sign3 : transformExpression Orbit.flip3 expression ≡ expression
open FixedAxisInvariantExpression public

jointMomentumSyntaxActionLevel : ProofLevel
jointMomentumSyntaxActionLevel = machineChecked

literalTrigParityUnderJointActionLevel : ProofLevel
literalTrigParityUnderJointActionLevel = machineChecked

literalHatMomentumScalarActionLevel : ProofLevel
literalHatMomentumScalarActionLevel = machineChecked

-- This is now a sharply source-specific leaf, not finite group algebra:
-- prove that scalarData.regularIntegrand, built from the literal Wilson/ghost/
-- Haar formulas, inhabits JointMomentumInvariantExpression; or if external p
-- is held on axis 0, inhabit FixedAxisInvariantExpression instead.  Round57's
-- exact geometric counts then determine whether the safe reduction is 240->4
-- or 240->7.
literalRegularIntegrandJointEquivarianceLevel : ProofLevel
literalRegularIntegrandJointEquivarianceLevel = conditional
