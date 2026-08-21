module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonLinkExponentialFourthJetExact where

------------------------------------------------------------------------
-- LITERAL ORIENTED SU(2) LINK FOUR-JET FOR THE WILSON ACTION
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10
-- (1974), 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", 2nd ed., Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- MATHEMATICAL CONTENT
--
-- For a positive oriented link U exp(t X), its nth derivative at t = 0 is
-- U X^n.  For the inverse occurrence exp(-t X) U^-1, it is
-- (-X)^n U^-1.  This file materializes those coefficients through order
-- four in the repository's rational quaternion carrier.  Thus the generic
-- four-link Leibniz engine receives literal Wilson cubic and quartic vertex
-- data; it does not receive those vertices as independent assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFourthJetExact as Wilson4

square cube fourthPower : Q.RationalQuaternion → Q.RationalQuaternion
square value = value Q.*q value
cube value = value Q.*q square value
fourthPower value = square value Q.*q square value

-- `base` is U and `generator` is the right-trivialized Lie-algebra element X.
positiveLinkExponentialJet4 :
  Q.RationalQuaternion → Q.RationalQuaternion → Wilson4.QuaternionFactorJet4
positiveLinkExponentialJet4 base generator = Wilson4.factorJet4
  base
  (base Q.*q generator)
  (base Q.*q square generator)
  (base Q.*q cube generator)
  (base Q.*q fourthPower generator)

-- `inverseBase` is U^-1.  Keeping left multiplication here is essential:
-- the inverse link is exp(-t X) U^-1, not U^-1 exp(-t X).
inverseLinkExponentialJet4 :
  Q.RationalQuaternion → Q.RationalQuaternion → Wilson4.QuaternionFactorJet4
inverseLinkExponentialJet4 inverseBase generator = Wilson4.factorJet4
  inverseBase
  (Q.negQ generator Q.*q inverseBase)
  (square generator Q.*q inverseBase)
  (Q.negQ (cube generator) Q.*q inverseBase)
  (fourthPower generator Q.*q inverseBase)

-- The coefficients are exposed separately so a literal plaquette AST can
-- consume exactly the coefficient demanded by its vertex, without a second
-- symbolic expansion of the same link path.
positiveLinkDerivative1 positiveLinkDerivative2 positiveLinkDerivative3
  positiveLinkDerivative4 :
  ∀ base generator → Q.RationalQuaternion
positiveLinkDerivative1 base generator =
  Wilson4.factor1 (positiveLinkExponentialJet4 base generator)
positiveLinkDerivative2 base generator =
  Wilson4.factor2 (positiveLinkExponentialJet4 base generator)
positiveLinkDerivative3 base generator =
  Wilson4.factor3 (positiveLinkExponentialJet4 base generator)
positiveLinkDerivative4 base generator =
  Wilson4.factor4 (positiveLinkExponentialJet4 base generator)

inverseLinkDerivative1 inverseLinkDerivative2 inverseLinkDerivative3
  inverseLinkDerivative4 :
  ∀ inverseBase generator → Q.RationalQuaternion
inverseLinkDerivative1 inverseBase generator =
  Wilson4.factor1 (inverseLinkExponentialJet4 inverseBase generator)
inverseLinkDerivative2 inverseBase generator =
  Wilson4.factor2 (inverseLinkExponentialJet4 inverseBase generator)
inverseLinkDerivative3 inverseBase generator =
  Wilson4.factor3 (inverseLinkExponentialJet4 inverseBase generator)
inverseLinkDerivative4 inverseBase generator =
  Wilson4.factor4 (inverseLinkExponentialJet4 inverseBase generator)

positiveLinkDerivative1Exact : ∀ base generator →
  positiveLinkDerivative1 base generator ≡ base Q.*q generator
positiveLinkDerivative1Exact base generator = refl

positiveLinkDerivative2Exact : ∀ base generator →
  positiveLinkDerivative2 base generator ≡ base Q.*q square generator
positiveLinkDerivative2Exact base generator = refl

positiveLinkDerivative3Exact : ∀ base generator →
  positiveLinkDerivative3 base generator ≡ base Q.*q cube generator
positiveLinkDerivative3Exact base generator = refl

positiveLinkDerivative4Exact : ∀ base generator →
  positiveLinkDerivative4 base generator ≡ base Q.*q fourthPower generator
positiveLinkDerivative4Exact base generator = refl

inverseLinkDerivative1Exact : ∀ inverseBase generator →
  inverseLinkDerivative1 inverseBase generator ≡ Q.negQ generator Q.*q inverseBase
inverseLinkDerivative1Exact inverseBase generator = refl

inverseLinkDerivative2Exact : ∀ inverseBase generator →
  inverseLinkDerivative2 inverseBase generator ≡ square generator Q.*q inverseBase
inverseLinkDerivative2Exact inverseBase generator = refl

inverseLinkDerivative3Exact : ∀ inverseBase generator →
  inverseLinkDerivative3 inverseBase generator
  ≡ Q.negQ (cube generator) Q.*q inverseBase
inverseLinkDerivative3Exact inverseBase generator = refl

inverseLinkDerivative4Exact : ∀ inverseBase generator →
  inverseLinkDerivative4 inverseBase generator ≡ fourthPower generator Q.*q inverseBase
inverseLinkDerivative4Exact inverseBase generator = refl

-- A literal positively oriented plaquette has two positive and two inverse
-- occurrences.  This is the concrete producer consumed by the cubic and
-- quartic Wilson coefficients in `BalabanP33RationalQuaternionWilsonFourthJetExact`.
literalOrientedPlaquetteFourthJet :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Wilson4.LiteralFourLinkWilsonFourthJet
literalOrientedPlaquetteFourthJet
  firstBase secondBase thirdInverse fourthInverse
  firstGenerator secondGenerator thirdGenerator fourthGenerator = record
  { Wilson4.link0 = positiveLinkExponentialJet4 firstBase firstGenerator
  ; Wilson4.link1 = positiveLinkExponentialJet4 secondBase secondGenerator
  ; Wilson4.link2 = inverseLinkExponentialJet4 thirdInverse thirdGenerator
  ; Wilson4.link3 = inverseLinkExponentialJet4 fourthInverse fourthGenerator
  }

literalSU2OrientedLinkFourthJetLevel : ProofLevel
-- Deliberately not promoted without a focused Agda check.  The mathematical
-- coefficients are definitionally explicit above; their use in beta
-- extraction remains conditional on the arbitrary-volume Fourier step.
literalSU2OrientedLinkFourthJetLevel = conditional

literalSU2WilsonCubicQuarticVertexProducerLevel : ProofLevel
literalSU2WilsonCubicQuarticVertexProducerLevel = conditional
