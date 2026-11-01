module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFourthJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
-- The existing literal quaternion plaquette lane stopped at the second
-- variation.  One-loop Wilson vertices require the cubic and quartic action
-- coefficients as well.  This module extends the SAME ordered four-link
-- quaternion product to derivatives 0..4 by the noncommutative Leibniz rule:
--
-- D3(ab) = a3 b + 3 a2 b1 + 3 a1 b2 + a b3,
-- D4(ab) = a4 b + 4 a3 b1 + 6 a2 b2 + 4 a1 b3 + a b4.
--
-- Nothing about a Feynman rule is postulated here.  Once each literal link
-- exponential supplies its first four one-link derivatives, the four-link
-- plaquette cubic/quartic Wilson coefficients are computed by these formulas.
-- This is the producer route to the Round57 literal one-loop AST.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; -_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact

record QuaternionFactorJet4 : Set where
  constructor factorJet4
  field
    factor0 factor1 factor2 factor3 factor4 : RationalQuaternion
open QuaternionFactorJet4 public

-- Exact natural multiplicities from the ordinary derivative Leibniz rule.
doubleQ tripleQ quadrupleQ sixQ : RationalQuaternion → RationalQuaternion
doubleQ q = q +q q
tripleQ q = q +q (q +q q)
quadrupleQ q = (q +q q) +q (q +q q)
sixQ q = tripleQ q +q tripleQ q

identityJet4 : QuaternionFactorJet4
identityJet4 = factorJet4 oneQ zeroQ zeroQ zeroQ zeroQ

multiplyJet4 : QuaternionFactorJet4 → QuaternionFactorJet4 → QuaternionFactorJet4
multiplyJet4 left right = factorJet4
  (factor0 left *q factor0 right)
  ((factor1 left *q factor0 right)
    +q (factor0 left *q factor1 right))
  ((factor2 left *q factor0 right)
    +q (doubleQ (factor1 left *q factor1 right)
      +q (factor0 left *q factor2 right)))
  ((factor3 left *q factor0 right)
    +q (tripleQ (factor2 left *q factor1 right)
      +q (tripleQ (factor1 left *q factor2 right)
        +q (factor0 left *q factor3 right))))
  ((factor4 left *q factor0 right)
    +q (quadrupleQ (factor3 left *q factor1 right)
      +q (sixQ (factor2 left *q factor2 right)
        +q (quadrupleQ (factor1 left *q factor3 right)
          +q (factor0 left *q factor4 right)))))

orderedProductJet4 : List QuaternionFactorJet4 → QuaternionFactorJet4
orderedProductJet4 [] = identityJet4
orderedProductJet4 (factor ∷ factors) =
  multiplyJet4 factor (orderedProductJet4 factors)

orderedValue4 orderedFirst4 orderedSecond4 orderedThird4 orderedFourth4 :
  List QuaternionFactorJet4 → RationalQuaternion
orderedValue4 factors = factor0 (orderedProductJet4 factors)
orderedFirst4 factors = factor1 (orderedProductJet4 factors)
orderedSecond4 factors = factor2 (orderedProductJet4 factors)
orderedThird4 factors = factor3 (orderedProductJet4 factors)
orderedFourth4 factors = factor4 (orderedProductJet4 factors)

fourFactorJets4 :
  QuaternionFactorJet4 → QuaternionFactorJet4 →
  QuaternionFactorJet4 → QuaternionFactorJet4 → List QuaternionFactorJet4
fourFactorJets4 first second third fourth =
  first ∷ second ∷ third ∷ fourth ∷ []

fourLinkWilsonCubicNumerator :
  QuaternionFactorJet4 → QuaternionFactorJet4 →
  QuaternionFactorJet4 → QuaternionFactorJet4 → ℚ
fourLinkWilsonCubicNumerator first second third fourth =
  - q0 (orderedThird4 (fourFactorJets4 first second third fourth))

fourLinkWilsonQuarticNumerator :
  QuaternionFactorJet4 → QuaternionFactorJet4 →
  QuaternionFactorJet4 → QuaternionFactorJet4 → ℚ
fourLinkWilsonQuarticNumerator first second third fourth =
  - q0 (orderedFourth4 (fourFactorJets4 first second third fourth))

-- Consumer-shaped data: this record does NOT accept cubic/quartic plaquette
-- vertices independently.  They are definitionally produced by the four link
-- jets, making a later Fourier AST trace back to the literal plaquette factors.
record LiteralFourLinkWilsonFourthJet : Set where
  field
    link0 link1 link2 link3 : QuaternionFactorJet4
open LiteralFourLinkWilsonFourthJet public

plaquetteValue plaquetteFirst plaquetteSecond plaquetteThird plaquetteFourth :
  LiteralFourLinkWilsonFourthJet → RationalQuaternion
plaquetteValue data = orderedValue4
  (fourFactorJets4 (link0 data) (link1 data) (link2 data) (link3 data))
plaquetteFirst data = orderedFirst4
  (fourFactorJets4 (link0 data) (link1 data) (link2 data) (link3 data))
plaquetteSecond data = orderedSecond4
  (fourFactorJets4 (link0 data) (link1 data) (link2 data) (link3 data))
plaquetteThird data = orderedThird4
  (fourFactorJets4 (link0 data) (link1 data) (link2 data) (link3 data))
plaquetteFourth data = orderedFourth4
  (fourFactorJets4 (link0 data) (link1 data) (link2 data) (link3 data))

wilsonCubicCoefficient wilsonQuarticCoefficient :
  LiteralFourLinkWilsonFourthJet → ℚ
wilsonCubicCoefficient data = - q0 (plaquetteThird data)
wilsonQuarticCoefficient data = - q0 (plaquetteFourth data)

rationalQuaternionLeibnizFourthJetLevel : ProofLevel
rationalQuaternionLeibnizFourthJetLevel = machineChecked

fourLinkWilsonCubicQuarticProducerLevel : ProofLevel
fourLinkWilsonCubicQuarticProducerLevel = machineChecked

-- Remaining physical leaf: instantiate each `factorJet4` with the literal
-- right/left oriented SU(2) link exponential through derivative order four.
-- Once that is done no independent Wilson cubic/quartic vertex input remains.
literalSU2LinkExponentialFourthJetInstantiationLevel : ProofLevel
literalSU2LinkExponentialFourthJetInstantiationLevel = conditional
