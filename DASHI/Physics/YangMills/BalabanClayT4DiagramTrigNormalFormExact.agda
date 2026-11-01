module DASHI.Physics.YangMills.BalabanClayT4DiagramTrigNormalFormExact where

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
-- Luis F. Abbott,
-- "The Background Field Method Beyond One Loop", Nuclear Physics B 185
-- (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Eliminate `hatMomentumSquared` as an independent transcendental atom before
-- interval evaluation.  The literal Wilson definition is
--
--   hat{k}^2 = 4 sum_mu sin^2(k_mu/2).
--
-- We therefore rewrite every hat-momentum atom into four sine-half squares.
-- This is deliberately the SAFE normalization currently justified by the
-- repository.  We do NOT rewrite further to 2(1-cos k): that requires the
-- still-unproved global/double-angle identity for the Bishop sine/cosine
-- series.  Once that identity is constructed it can be added as a second
-- normalization theorem without changing the diagram evaluator.
--
-- The recursive semantic theorem below says that one literal hat-momentum
-- identity per momentum role is enough to justify the rewrite for EVERY
-- Wilson/ghost/Haar diagram expression.  Thus the 240-box evaluator no longer
-- needs a separate semantic hat{k}^2 oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval

four : ℚ
four = + 4 / 1

axisList : List Eval.AxisIndex
axisList = Eval.axis0 ∷ Eval.axis1 ∷ Eval.axis2 ∷ Eval.axis3 ∷ []

squareExpression : Eval.DiagramExpression → Eval.DiagramExpression
squareExpression expression = Eval.multiply expression expression

fourSineHalfSquare :
  Eval.MomentumRole → Eval.AxisIndex → Eval.DiagramExpression
fourSineHalfSquare role axis =
  Eval.multiply
    (Eval.rationalConstant four)
    (squareExpression (Eval.atom (Eval.sineHalf role axis)))

expandedHatMomentumSquared :
  Eval.MomentumRole → Eval.DiagramExpression
expandedHatMomentumSquared role =
  Eval.sumExpressions
    ( fourSineHalfSquare role Eval.axis0
    ∷ fourSineHalfSquare role Eval.axis1
    ∷ fourSineHalfSquare role Eval.axis2
    ∷ fourSineHalfSquare role Eval.axis3
    ∷ [] )

normalizeHatMomentum : Eval.DiagramExpression → Eval.DiagramExpression
normalizeHatMomentum (Eval.rationalConstant value) =
  Eval.rationalConstant value
normalizeHatMomentum (Eval.atom (Eval.sineHalf role axis)) =
  Eval.atom (Eval.sineHalf role axis)
normalizeHatMomentum (Eval.atom (Eval.cosineFull role axis)) =
  Eval.atom (Eval.cosineFull role axis)
normalizeHatMomentum (Eval.atom (Eval.hatMomentumSquared role)) =
  expandedHatMomentumSquared role
normalizeHatMomentum (Eval.atom Eval.colorCasimir) =
  Eval.atom Eval.colorCasimir
normalizeHatMomentum (Eval.atom Eval.gaugeParameter) =
  Eval.atom Eval.gaugeParameter
normalizeHatMomentum (Eval.add left right) =
  Eval.add (normalizeHatMomentum left) (normalizeHatMomentum right)
normalizeHatMomentum (Eval.subtract left right) =
  Eval.subtract (normalizeHatMomentum left) (normalizeHatMomentum right)
normalizeHatMomentum (Eval.multiply left right) =
  Eval.multiply (normalizeHatMomentum left) (normalizeHatMomentum right)
normalizeHatMomentum (Eval.divide left right) =
  Eval.divide (normalizeHatMomentum left) (normalizeHatMomentum right)
normalizeHatMomentum (Eval.negate value) =
  Eval.negate (normalizeHatMomentum value)

------------------------------------------------------------------------
-- Literal semantics and recursive correctness.
------------------------------------------------------------------------

record DiagramSemantics (Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    atomValue : Eval.TrigAtom → Scalar
    add subtract multiply divide : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
open DiagramSemantics public

interpret :
  ∀ {Scalar} → DiagramSemantics Scalar → Eval.DiagramExpression → Scalar
interpret semantics (Eval.rationalConstant value) = rational semantics value
interpret semantics (Eval.atom trigAtom) = atomValue semantics trigAtom
interpret semantics (Eval.add left right) =
  add semantics (interpret semantics left) (interpret semantics right)
interpret semantics (Eval.subtract left right) =
  subtract semantics (interpret semantics left) (interpret semantics right)
interpret semantics (Eval.multiply left right) =
  multiply semantics (interpret semantics left) (interpret semantics right)
interpret semantics (Eval.divide left right) =
  divide semantics (interpret semantics left) (interpret semantics right)
interpret semantics (Eval.negate value) =
  negate semantics (interpret semantics value)

record LiteralHatMomentumSemantics
    {Scalar : Set} (semantics : DiagramSemantics Scalar) : Set₁ where
  field
    hatMomentumSquaredExact : ∀ role →
      atomValue semantics (Eval.hatMomentumSquared role)
      ≡ interpret semantics (expandedHatMomentumSquared role)
open LiteralHatMomentumSemantics public

normalizeHatMomentumSound :
  ∀ {Scalar}
    {semantics : DiagramSemantics Scalar} →
  LiteralHatMomentumSemantics semantics →
  ∀ expression →
  interpret semantics expression
  ≡ interpret semantics (normalizeHatMomentum expression)
normalizeHatMomentumSound literal (Eval.rationalConstant value) = refl
normalizeHatMomentumSound literal (Eval.atom (Eval.sineHalf role axis)) = refl
normalizeHatMomentumSound literal (Eval.atom (Eval.cosineFull role axis)) = refl
normalizeHatMomentumSound literal (Eval.atom (Eval.hatMomentumSquared role)) =
  hatMomentumSquaredExact literal role
normalizeHatMomentumSound literal (Eval.atom Eval.colorCasimir) = refl
normalizeHatMomentumSound literal (Eval.atom Eval.gaugeParameter) = refl
normalizeHatMomentumSound {semantics = semantics} literal (Eval.add left right) =
  cong₂ (add semantics)
    (normalizeHatMomentumSound literal left)
    (normalizeHatMomentumSound literal right)
normalizeHatMomentumSound {semantics = semantics} literal (Eval.subtract left right) =
  cong₂ (subtract semantics)
    (normalizeHatMomentumSound literal left)
    (normalizeHatMomentumSound literal right)
normalizeHatMomentumSound {semantics = semantics} literal (Eval.multiply left right) =
  cong₂ (multiply semantics)
    (normalizeHatMomentumSound literal left)
    (normalizeHatMomentumSound literal right)
normalizeHatMomentumSound {semantics = semantics} literal (Eval.divide left right) =
  cong₂ (divide semantics)
    (normalizeHatMomentumSound literal left)
    (normalizeHatMomentumSound literal right)
normalizeHatMomentumSound {semantics = semantics} literal (Eval.negate value) =
  cong (negate semantics) (normalizeHatMomentumSound literal value)

------------------------------------------------------------------------
-- Mechanical normal-form check: no hatMomentumSquared atom survives.
------------------------------------------------------------------------

_and_ : Bool → Bool → Bool
true and value = value
false and value = false

hatFreeAtom : Eval.TrigAtom → Bool
hatFreeAtom (Eval.sineHalf role axis) = true
hatFreeAtom (Eval.cosineFull role axis) = true
hatFreeAtom (Eval.hatMomentumSquared role) = false
hatFreeAtom Eval.colorCasimir = true
hatFreeAtom Eval.gaugeParameter = true

hatFree : Eval.DiagramExpression → Bool
hatFree (Eval.rationalConstant value) = true
hatFree (Eval.atom trigAtom) = hatFreeAtom trigAtom
hatFree (Eval.add left right) = hatFree left and hatFree right
hatFree (Eval.subtract left right) = hatFree left and hatFree right
hatFree (Eval.multiply left right) = hatFree left and hatFree right
hatFree (Eval.divide left right) = hatFree left and hatFree right
hatFree (Eval.negate value) = hatFree value

expandedHatMomentumSquaredIsHatFree : ∀ role →
  hatFree (expandedHatMomentumSquared role) ≡ true
expandedHatMomentumSquaredIsHatFree role = refl

normalizeHatMomentumIsHatFree : ∀ expression →
  hatFree (normalizeHatMomentum expression) ≡ true
normalizeHatMomentumIsHatFree (Eval.rationalConstant value) = refl
normalizeHatMomentumIsHatFree (Eval.atom (Eval.sineHalf role axis)) = refl
normalizeHatMomentumIsHatFree (Eval.atom (Eval.cosineFull role axis)) = refl
normalizeHatMomentumIsHatFree (Eval.atom (Eval.hatMomentumSquared role)) = refl
normalizeHatMomentumIsHatFree (Eval.atom Eval.colorCasimir) = refl
normalizeHatMomentumIsHatFree (Eval.atom Eval.gaugeParameter) = refl
normalizeHatMomentumIsHatFree (Eval.add left right)
  rewrite normalizeHatMomentumIsHatFree left
        | normalizeHatMomentumIsHatFree right = refl
normalizeHatMomentumIsHatFree (Eval.subtract left right)
  rewrite normalizeHatMomentumIsHatFree left
        | normalizeHatMomentumIsHatFree right = refl
normalizeHatMomentumIsHatFree (Eval.multiply left right)
  rewrite normalizeHatMomentumIsHatFree left
        | normalizeHatMomentumIsHatFree right = refl
normalizeHatMomentumIsHatFree (Eval.divide left right)
  rewrite normalizeHatMomentumIsHatFree left
        | normalizeHatMomentumIsHatFree right = refl
normalizeHatMomentumIsHatFree (Eval.negate value) =
  normalizeHatMomentumIsHatFree value

literalHatMomentumSyntaxNormalizationLevel : ProofLevel
literalHatMomentumSyntaxNormalizationLevel = machineChecked

literalHatMomentumRecursiveSemanticTransportLevel : ProofLevel
literalHatMomentumRecursiveSemanticTransportLevel = machineChecked

-- Remaining semantic leaf: instantiate `hatMomentumSquaredExact` from the
-- literal Wilson lattice momentum in the Bishop-real carrier.  This is one
-- source identity per momentum role, not one assumption per box.
literalWilsonHatMomentumBishopIdentificationLevel : ProofLevel
literalWilsonHatMomentumBishopIdentificationLevel = conditional

-- Optional cosine-only normalization remains blocked specifically by the
-- Bishop sine/cosine addition/double-angle theorem; it is not required for the
-- safe sine-half normal form above.
bishopDoubleAngleCosineNormalizationLevel : ProofLevel
bishopDoubleAngleCosineNormalizationLevel = conditional
