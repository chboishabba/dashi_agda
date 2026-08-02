module DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusFromSignedTailsExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4AlternatingTaylorEnvelopeExact as Taylor
import DASHI.Physics.YangMills.BalabanClayGate4SU2HalfRadiusScalarEnvelopeExact as HalfRadius

------------------------------------------------------------------------
-- Build the SU(2) half-radius scalar envelope from signed series tails.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations", second edition,
-- Springer (2015). DOI: 10.1007/978-3-319-13467-3.
--
-- The previous interface accepted the final sinc, cosc and dexp^{-1}
-- inequalities.  This adapter lowers the proof boundary to the constructive
-- alternating-series facts: the signs of the first remainders and a positive
-- Bernoulli tail.  Absolute-value bounds are derived by the generic Taylor
-- envelope theorem.
------------------------------------------------------------------------

record SU2HalfRadiusScalarCore (Scalar : Set) : Set₁ where
  field
    coreScalar : HalfRadius.OrderedTrigScalar Scalar

    coreHalf coreOneHalf coreOneSixth coreOneTwelfth
      coreOneTwentyFourth : Scalar

    coreHalfMeaning :
      HalfRadius.Equivalent coreScalar coreHalf
        (HalfRadius.divide coreScalar
          (HalfRadius.one coreScalar) (HalfRadius.two coreScalar))
    coreOneHalfMeaning :
      HalfRadius.Equivalent coreScalar coreOneHalf
        (HalfRadius.divide coreScalar
          (HalfRadius.one coreScalar) (HalfRadius.two coreScalar))
    coreOneSixthMeaning :
      HalfRadius.Equivalent coreScalar coreOneSixth
        (HalfRadius.divide coreScalar
          (HalfRadius.one coreScalar) (HalfRadius.six coreScalar))
    coreOneTwelfthMeaning :
      HalfRadius.Equivalent coreScalar coreOneTwelfth
        (HalfRadius.divide coreScalar
          (HalfRadius.one coreScalar) (HalfRadius.twelve coreScalar))
    coreOneTwentyFourthMeaning :
      HalfRadius.Equivalent coreScalar coreOneTwentyFourth
        (HalfRadius.divide coreScalar
          (HalfRadius.one coreScalar) (HalfRadius.twentyFour coreScalar))

    CoreInsideHalfBall : Scalar → Set
    coreInsideNonnegative : ∀ theta → CoreInsideHalfBall theta →
      HalfRadius.LessEqual coreScalar (HalfRadius.zero coreScalar) theta
    coreInsideBelowHalf : ∀ theta → CoreInsideHalfBall theta →
      HalfRadius.LessEqual coreScalar theta coreHalf

    coreSinc coreCosc coreInverseDexpQuadratic : Scalar → Scalar

    coreSincAtZero :
      HalfRadius.Equivalent coreScalar
        (coreSinc (HalfRadius.zero coreScalar))
        (HalfRadius.one coreScalar)
    coreCoscAtZero :
      HalfRadius.Equivalent coreScalar
        (coreCosc (HalfRadius.zero coreScalar)) coreOneHalf
    coreInverseDexpQuadraticAtZero :
      HalfRadius.Equivalent coreScalar
        (coreInverseDexpQuadratic (HalfRadius.zero coreScalar))
        coreOneTwelfth

    coreSincAwayFromZero : ∀ theta →
      HalfRadius.Nonzero coreScalar theta →
      HalfRadius.Equivalent coreScalar (coreSinc theta)
        (HalfRadius.divide coreScalar
          (HalfRadius.sine coreScalar theta) theta)

    coreCoscAwayFromZero : ∀ theta →
      HalfRadius.Nonzero coreScalar theta →
      HalfRadius.Equivalent coreScalar (coreCosc theta)
        (HalfRadius.divide coreScalar
          (HalfRadius.subtract coreScalar
            (HalfRadius.one coreScalar)
            (HalfRadius.cosine coreScalar theta))
          (HalfRadius.multiply coreScalar theta theta))

    coreInverseDexpAwayFromZero : ∀ theta →
      HalfRadius.Nonzero coreScalar theta →
      HalfRadius.Equivalent coreScalar
        (coreInverseDexpQuadratic theta)
        (HalfRadius.subtract coreScalar
          (HalfRadius.divide coreScalar
            (HalfRadius.one coreScalar)
            (HalfRadius.multiply coreScalar theta theta))
          (HalfRadius.divide coreScalar
            (HalfRadius.add coreScalar
              (HalfRadius.one coreScalar)
              (HalfRadius.cosine coreScalar theta))
            (HalfRadius.multiply coreScalar
              (HalfRadius.two coreScalar)
              (HalfRadius.multiply coreScalar theta
                (HalfRadius.sine coreScalar theta)))))

    coreInverseDexpSlack : Scalar

    coreAdLipschitz coreDexpLipschitz coreDexpInverseLipschitz : Scalar
    CoreAdDifference CoreDexpDifference CoreDexpInverseDifference :
      Scalar → Scalar → Set

    coreAdDifferenceBound : ∀ left right →
      CoreInsideHalfBall left → CoreInsideHalfBall right →
      CoreAdDifference left right
    coreDexpDifferenceBound : ∀ left right →
      CoreInsideHalfBall left → CoreInsideHalfBall right →
      CoreDexpDifference left right
    coreDexpInverseDifferenceBound : ∀ left right →
      CoreInsideHalfBall left → CoreInsideHalfBall right →
      CoreDexpInverseDifference left right

open SU2HalfRadiusScalarCore public

record CoreOrderedAbsoluteLaws
    {Scalar : Set} (core : SU2HalfRadiusScalarCore Scalar) : Set₁ where
  field
    coreAbsoluteCong : ∀ {left right} →
      HalfRadius.Equivalent (coreScalar core) left right →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.absolute (coreScalar core) left)
        (HalfRadius.absolute (coreScalar core) right)

    coreAbsoluteNegate : ∀ value →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.absolute (coreScalar core)
          (HalfRadius.negate (coreScalar core) value))
        (HalfRadius.absolute (coreScalar core) value)

    coreAbsoluteOfNonnegative : ∀ {value} →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) value →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.absolute (coreScalar core) value) value

    coreSubtractNonnegative : ∀ {small large} →
      HalfRadius.LessEqual (coreScalar core) small large →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core))
        (HalfRadius.subtract (coreScalar core) large small)

    coreSubtractBelowLeft : ∀ {small large} →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) small →
      HalfRadius.LessEqual (coreScalar core) small large →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.subtract (coreScalar core) large small) large

    coreAddNonnegative : ∀ {left right} →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) left →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) right →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core))
        (HalfRadius.add (coreScalar core) left right)

    coreAddMonotone : ∀ {left leftUpper right rightUpper} →
      HalfRadius.LessEqual (coreScalar core) left leftUpper →
      HalfRadius.LessEqual (coreScalar core) right rightUpper →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.add (coreScalar core) left right)
        (HalfRadius.add (coreScalar core) leftUpper rightUpper)

open CoreOrderedAbsoluteLaws public

asOrderedAbsoluteAlgebra :
  ∀ {Scalar} {core : SU2HalfRadiusScalarCore Scalar} →
  CoreOrderedAbsoluteLaws core → Taylor.OrderedAbsoluteAlgebra Scalar
asOrderedAbsoluteAlgebra {core = core} laws = record
  { Taylor.OrderedAbsoluteAlgebra.zero =
      HalfRadius.zero (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.add =
      HalfRadius.add (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.subtract =
      HalfRadius.subtract (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.negate =
      HalfRadius.negate (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.absolute =
      HalfRadius.absolute (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.Equivalent =
      HalfRadius.Equivalent (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.LessEqual =
      HalfRadius.LessEqual (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.equivalentRefl =
      HalfRadius.equivalentRefl (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.equivalentSym =
      HalfRadius.equivalentSym (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.equivalentTrans =
      HalfRadius.equivalentTrans (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.reflexive =
      HalfRadius.reflexive (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.transitive =
      HalfRadius.transitive (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.lessEqualResp =
      HalfRadius.lessEqualResp (coreScalar core)
  ; Taylor.OrderedAbsoluteAlgebra.absoluteCong = coreAbsoluteCong laws
  ; Taylor.OrderedAbsoluteAlgebra.absoluteNegate = coreAbsoluteNegate laws
  ; Taylor.OrderedAbsoluteAlgebra.absoluteOfNonnegative =
      coreAbsoluteOfNonnegative laws
  ; Taylor.OrderedAbsoluteAlgebra.subtractNonnegative =
      coreSubtractNonnegative laws
  ; Taylor.OrderedAbsoluteAlgebra.subtractBelowLeft =
      coreSubtractBelowLeft laws
  ; Taylor.OrderedAbsoluteAlgebra.addNonnegative = coreAddNonnegative laws
  ; Taylor.OrderedAbsoluteAlgebra.addMonotone = coreAddMonotone laws
  }

record SU2HalfRadiusSignedTailInputs
    {Scalar : Set} (core : SU2HalfRadiusScalarCore Scalar) : Set₁ where
  field
    absoluteLaws : CoreOrderedAbsoluteLaws core

    sincRemainder coscRemainder : Scalar → Scalar
    inverseLeading inverseRemainder inverseTailBudget : Scalar → Scalar

    sincRemainderNonnegative : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) (sincRemainder theta)
    sincRemainderBelowLeading : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (sincRemainder theta)
        (HalfRadius.multiply (coreScalar core) (coreOneSixth core)
          (HalfRadius.multiply (coreScalar core) theta theta))
    sincSignedDifference : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.subtract (coreScalar core)
          (coreSinc core theta) (HalfRadius.one (coreScalar core)))
        (HalfRadius.negate (coreScalar core)
          (HalfRadius.subtract (coreScalar core)
            (HalfRadius.multiply (coreScalar core) (coreOneSixth core)
              (HalfRadius.multiply (coreScalar core) theta theta))
            (sincRemainder theta)))

    coscRemainderNonnegative : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) (coscRemainder theta)
    coscRemainderBelowLeading : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (coscRemainder theta)
        (HalfRadius.multiply (coreScalar core) (coreOneTwentyFourth core)
          (HalfRadius.multiply (coreScalar core) theta theta))
    coscSignedDifference : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.subtract (coreScalar core)
          (coreCosc core theta) (coreOneHalf core))
        (HalfRadius.negate (coreScalar core)
          (HalfRadius.subtract (coreScalar core)
            (HalfRadius.multiply (coreScalar core)
              (coreOneTwentyFourth core)
              (HalfRadius.multiply (coreScalar core) theta theta))
            (coscRemainder theta)))

    inverseLeadingNonnegative : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) (inverseLeading theta)
    inverseRemainderNonnegative : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.zero (coreScalar core)) (inverseRemainder theta)
    inverseRemainderBelowTail : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (inverseRemainder theta) (inverseTailBudget theta)
    inversePositiveDifference : ∀ theta → CoreInsideHalfBall core theta →
      HalfRadius.Equivalent (coreScalar core)
        (HalfRadius.subtract (coreScalar core)
          (coreInverseDexpQuadratic core theta) (coreOneTwelfth core))
        (HalfRadius.add (coreScalar core)
          (inverseLeading theta) (inverseRemainder theta))
    inverseLeadingAndTailBelowSlack : ∀ theta →
      CoreInsideHalfBall core theta →
      HalfRadius.LessEqual (coreScalar core)
        (HalfRadius.add (coreScalar core)
          (inverseLeading theta) (inverseTailBudget theta))
        (HalfRadius.multiply (coreScalar core)
          (coreInverseDexpSlack core)
          (HalfRadius.multiply (coreScalar core) theta theta))

open SU2HalfRadiusSignedTailInputs public

sincCertificate :
  ∀ {Scalar} {core : SU2HalfRadiusScalarCore Scalar}
    (tails : SU2HalfRadiusSignedTailInputs core)
    theta → CoreInsideHalfBall core theta →
  Taylor.AlternatingFirstOmittedCertificate
    (asOrderedAbsoluteAlgebra (absoluteLaws tails))
sincCertificate {core = core} tails theta inside = record
  { Taylor.AlternatingFirstOmittedCertificate.value = coreSinc core theta
  ; Taylor.AlternatingFirstOmittedCertificate.centre =
      HalfRadius.one (coreScalar core)
  ; Taylor.AlternatingFirstOmittedCertificate.leading =
      HalfRadius.multiply (coreScalar core) (coreOneSixth core)
        (HalfRadius.multiply (coreScalar core) theta theta)
  ; Taylor.AlternatingFirstOmittedCertificate.remainder =
      sincRemainder tails theta
  ; Taylor.AlternatingFirstOmittedCertificate.remainderNonnegative =
      sincRemainderNonnegative tails theta inside
  ; Taylor.AlternatingFirstOmittedCertificate.remainderBelowLeading =
      sincRemainderBelowLeading tails theta inside
  ; Taylor.AlternatingFirstOmittedCertificate.signedDifferenceMeaning =
      sincSignedDifference tails theta inside
  }

coscCertificate :
  ∀ {Scalar} {core : SU2HalfRadiusScalarCore Scalar}
    (tails : SU2HalfRadiusSignedTailInputs core)
    theta → CoreInsideHalfBall core theta →
  Taylor.AlternatingFirstOmittedCertificate
    (asOrderedAbsoluteAlgebra (absoluteLaws tails))
coscCertificate {core = core} tails theta inside = record
  { Taylor.AlternatingFirstOmittedCertificate.value = coreCosc core theta
  ; Taylor.AlternatingFirstOmittedCertificate.centre = coreOneHalf core
  ; Taylor.AlternatingFirstOmittedCertificate.leading =
      HalfRadius.multiply (coreScalar core) (coreOneTwentyFourth core)
        (HalfRadius.multiply (coreScalar core) theta theta)
  ; Taylor.AlternatingFirstOmittedCertificate.remainder =
      coscRemainder tails theta
  ; Taylor.AlternatingFirstOmittedCertificate.remainderNonnegative =
      coscRemainderNonnegative tails theta inside
  ; Taylor.AlternatingFirstOmittedCertificate.remainderBelowLeading =
      coscRemainderBelowLeading tails theta inside
  ; Taylor.AlternatingFirstOmittedCertificate.signedDifferenceMeaning =
      coscSignedDifference tails theta inside
  }

inverseCertificate :
  ∀ {Scalar} {core : SU2HalfRadiusScalarCore Scalar}
    (tails : SU2HalfRadiusSignedTailInputs core)
    theta → CoreInsideHalfBall core theta →
  Taylor.PositiveTaylorTailCertificate
    (asOrderedAbsoluteAlgebra (absoluteLaws tails))
inverseCertificate {core = core} tails theta inside = record
  { Taylor.PositiveTaylorTailCertificate.value =
      coreInverseDexpQuadratic core theta
  ; Taylor.PositiveTaylorTailCertificate.centre = coreOneTwelfth core
  ; Taylor.PositiveTaylorTailCertificate.leading = inverseLeading tails theta
  ; Taylor.PositiveTaylorTailCertificate.remainder = inverseRemainder tails theta
  ; Taylor.PositiveTaylorTailCertificate.tailBudget = inverseTailBudget tails theta
  ; Taylor.PositiveTaylorTailCertificate.leadingNonnegative =
      inverseLeadingNonnegative tails theta inside
  ; Taylor.PositiveTaylorTailCertificate.remainderNonnegative =
      inverseRemainderNonnegative tails theta inside
  ; Taylor.PositiveTaylorTailCertificate.remainderBelowTailBudget =
      inverseRemainderBelowTail tails theta inside
  ; Taylor.PositiveTaylorTailCertificate.positiveDifferenceMeaning =
      inversePositiveDifference tails theta inside
  }

halfRadiusEnvelopeFromSignedTails :
  ∀ {Scalar} {core : SU2HalfRadiusScalarCore Scalar} →
  SU2HalfRadiusSignedTailInputs core →
  HalfRadius.SU2HalfRadiusScalarEnvelope Scalar
halfRadiusEnvelopeFromSignedTails {core = core} tails = record
  { HalfRadius.SU2HalfRadiusScalarEnvelope.scalar = coreScalar core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.half = coreHalf core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneHalf = coreOneHalf core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneSixth = coreOneSixth core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneTwelfth = coreOneTwelfth core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneTwentyFourth =
      coreOneTwentyFourth core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.halfMeaning = coreHalfMeaning core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneHalfMeaning =
      coreOneHalfMeaning core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneSixthMeaning =
      coreOneSixthMeaning core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneTwelfthMeaning =
      coreOneTwelfthMeaning core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.oneTwentyFourthMeaning =
      coreOneTwentyFourthMeaning core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.InsideHalfBall =
      CoreInsideHalfBall core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.insideImpliesNonnegative =
      coreInsideNonnegative core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.insideImpliesBelowHalf =
      coreInsideBelowHalf core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.sinc = coreSinc core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.cosc = coreCosc core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.inverseDexpQuadratic =
      coreInverseDexpQuadratic core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.sincAtZero = coreSincAtZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.coscAtZero = coreCoscAtZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.inverseDexpQuadraticAtZero =
      coreInverseDexpQuadraticAtZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.sincMeaningAwayFromZero =
      coreSincAwayFromZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.coscMeaningAwayFromZero =
      coreCoscAwayFromZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.inverseDexpQuadraticMeaningAwayFromZero =
      coreInverseDexpAwayFromZero core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.sincTaylorBound =
      λ theta inside →
        Taylor.alternatingFirstOmittedAbsoluteBound
          (sincCertificate tails theta inside)
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.coscTaylorBound =
      λ theta inside →
        Taylor.alternatingFirstOmittedAbsoluteBound
          (coscCertificate tails theta inside)
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.inverseDexpQuadraticSlack =
      coreInverseDexpSlack core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.inverseDexpQuadraticTaylorBound =
      λ theta inside →
        HalfRadius.transitive (coreScalar core)
          (Taylor.positiveTailAbsoluteBound
            (inverseCertificate tails theta inside))
          (inverseLeadingAndTailBelowSlack tails theta inside)
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.adCoefficientLipschitz =
      coreAdLipschitz core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.dexpCoefficientLipschitz =
      coreDexpLipschitz core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.dexpInverseCoefficientLipschitz =
      coreDexpInverseLipschitz core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.AdCoefficientDifference =
      CoreAdDifference core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.DexpCoefficientDifference =
      CoreDexpDifference core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.DexpInverseCoefficientDifference =
      CoreDexpInverseDifference core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.adCoefficientDifferenceBound =
      coreAdDifferenceBound core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.dexpCoefficientDifferenceBound =
      coreDexpDifferenceBound core
  ; HalfRadius.SU2HalfRadiusScalarEnvelope.dexpInverseCoefficientDifferenceBound =
      coreDexpInverseDifferenceBound core
  }

su2HalfRadiusSignedTailConstructionLevel : ProofLevel
su2HalfRadiusSignedTailConstructionLevel = machineChecked

su2HalfRadiusTaylorInequalitiesDerivedLevel : ProofLevel
su2HalfRadiusTaylorInequalitiesDerivedLevel = machineChecked

physicalBishopSignedTailInputsLevel : ProofLevel
physicalBishopSignedTailInputsLevel = conditional
