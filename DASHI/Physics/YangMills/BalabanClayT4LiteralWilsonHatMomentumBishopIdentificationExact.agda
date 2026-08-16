module DASHI.Physics.YangMills.BalabanClayT4LiteralWilsonHatMomentumBishopIdentificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", B.Sc. Honours thesis,
-- Dalhousie University, 2022, arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- This is the requested L3/3a semantic identification.  The `hatMomentumSquared`
-- atom of the canonical Bishop environment is not a separately supplied
-- number: it is definitionally the Wilson lattice momentum
--
--       4 sum_{mu=0}^3 sin^2(k_mu/2)
--
-- built from the SAME physical sine-half values.  We also prove its
-- constructive nonnegativity directly from square nonnegativity.  The shifted
-- momentum role uses the same theorem, so no second propagator definition is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
open import DASHI.Physics.YangMills.CompactLieProofLevel

literalWilsonHatMomentum :
  Canonical.PhysicalTrigBoxData → Eval.MomentumRole → Bishop.ℝ
literalWilsonHatMomentum dataSet role =
  let
    s0 = Canonical.sineHalfValue dataSet role Eval.axis0
    s1 = Canonical.sineHalfValue dataSet role Eval.axis1
    s2 = Canonical.sineHalfValue dataSet role Eval.axis2
    s3 = Canonical.sineHalfValue dataSet role Eval.axis3
    four = Canonical.fourValue
  in
  (four Bishop.* (s0 Bishop.* s0)) Bishop.+
  (four Bishop.* (s1 Bishop.* s1)) Bishop.+
  (four Bishop.* (s2 Bishop.* s2)) Bishop.+
  (four Bishop.* (s3 Bishop.* s3))

hatMomentumValueIsLiteralWilson : ∀ dataSet role →
  Canonical.hatMomentumValue dataSet role
  ≡ literalWilsonHatMomentum dataSet role
hatMomentumValueIsLiteralWilson dataSet role = refl

-- The actual atom exposed to the expression evaluator is the same object.
hatMomentumAtomValueIsLiteralWilson : ∀ dataSet role →
  Canonical.canonicalAtomValue dataSet (Eval.hatMomentumSquared role)
  ≡ literalWilsonHatMomentum dataSet role
hatMomentumAtomValueIsLiteralWilson dataSet role = refl

squareNonnegative : ∀ value → Bishop.NonNegative (value Bishop.* value)
squareNonnegative value = BishopP.nonNegSquare value

scaledSquareNonnegative : ∀ value →
  Bishop.NonNegative (Canonical.fourValue Bishop.* (value Bishop.* value))
scaledSquareNonnegative value =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.0≤x⇒nonNegx
      (BishopP.p≤q⇒p⋆≤q⋆
        Data.Rational.Unnormalised.0ℚᵘ
        (Data.Rational.Base.toℚᵘ Canonical.fourRational)
        (Data.Rational.Unnormalised.Properties.nonNegative⁻¹
          (Data.Rational.Base.toℚᵘ Canonical.fourRational))))
    (squareNonnegative value)

literalWilsonHatMomentumNonnegative : ∀ dataSet role →
  Bishop.NonNegative (literalWilsonHatMomentum dataSet role)
literalWilsonHatMomentumNonnegative dataSet role =
  let
    s0 = Canonical.sineHalfValue dataSet role Eval.axis0
    s1 = Canonical.sineHalfValue dataSet role Eval.axis1
    s2 = Canonical.sineHalfValue dataSet role Eval.axis2
    s3 = Canonical.sineHalfValue dataSet role Eval.axis3
    n0 = scaledSquareNonnegative s0
    n1 = scaledSquareNonnegative s1
    n2 = scaledSquareNonnegative s2
    n3 = scaledSquareNonnegative s3
  in
  BishopP.nonNegx,y⇒nonNegx+y
    (BishopP.nonNegx,y⇒nonNegx+y
      (BishopP.nonNegx,y⇒nonNegx+y n0 n1)
      n2)
    n3

hatMomentumAtomNonnegative : ∀ dataSet role →
  Bishop.NonNegative
    (Canonical.canonicalAtomValue dataSet (Eval.hatMomentumSquared role))
hatMomentumAtomNonnegative = literalWilsonHatMomentumNonnegative

literalWilsonHatMomentumBishopIdentificationLevel : ProofLevel
literalWilsonHatMomentumBishopIdentificationLevel = machineChecked

literalWilsonHatMomentumNonnegativeLevel : ProofLevel
literalWilsonHatMomentumNonnegativeLevel = machineChecked
