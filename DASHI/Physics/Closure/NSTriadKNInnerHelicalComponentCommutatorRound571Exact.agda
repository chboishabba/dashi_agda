module DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact where

------------------------------------------------------------------------
-- ROUND571 / RAW INNER PAIR -> FOUR HELICAL MULTIPLIER-DIFFERENCE PAIRS
--
-- R310 exposes the useful inner p-fibre pairing but its strongest historical
-- normal form asks for each RAW velocity pair to be a curl eigenpair.  That is
-- too strong for an arbitrary physical Navier--Stokes velocity.
--
-- The repository already owns the correct weaker route:
--
--   u_a = u_a+ + u_a-,    u_b = u_b+ + u_b-
--
-- on transverse physical modes (helical projector laws), and R82 proves exact
-- bilinearity of the literal ordered Galerkin interaction.  Therefore the
-- symmetrised ordered pair expands into the four sign pairs
--
--   (++), (+-), (-+), (--).
--
-- Each projected component is itself an exact curl eigenvector, so R106 applies
-- to each sign pair directly and gives the multiplier-difference vector
--
--   (lambda_b^t - lambda_a^s) P_p (u_a^s x u_b^t).
--
-- Thus the useful inner multiplier-difference structure does NOT require the
-- raw physical velocity to be helical.  No estimate, shell count, absolute
-- value, or cancellation claim is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as R82
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120

------------------------------------------------------------------------
-- 1. Ordered-pair bilinearity derived from the already-proved ordered-term
--    bilinearity in R82.
------------------------------------------------------------------------

pairInteraction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
pairInteraction {F = F} E I k p q =
  Signed.orderedPairVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I) k p q

pairAddLeft :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (u v w : C3.Complex3 F) →
  pairInteraction E I k p q (C3.complex3Add u v) w
  ≡ C3.complex3Add
      (pairInteraction E I k p q u w)
      (pairInteraction E I k p q v w)
pairAddLeft {F = F} E I k p q u v w =
  let
    A = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u w
    B = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q v w
    C = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k q p w u
    D = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k q p w v
  in
  trans
    (cong₂ C3.complex3Add
      (R82.orderedInteractionAddLeft E I k p q u v w)
      (R82.orderedInteractionAddRight E I k q p w u v))
    (R82.complex3Interchange A B C D)

pairAddRight :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (u v w : C3.Complex3 F) →
  pairInteraction E I k p q u (C3.complex3Add v w)
  ≡ C3.complex3Add
      (pairInteraction E I k p q u v)
      (pairInteraction E I k p q u w)
pairAddRight {F = F} E I k p q u v w =
  let
    A = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u v
    B = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u w
    C = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k q p v u
    D = Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k q p w u
  in
  trans
    (cong₂ C3.complex3Add
      (R82.orderedInteractionAddRight E I k p q u v w)
      (R82.orderedInteractionAddLeft E I k q p v w u))
    (R82.complex3Interchange A B C D)

------------------------------------------------------------------------
-- 2. Componentwise helical data for an arbitrary transverse physical field.
------------------------------------------------------------------------

module Componentwise
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  velocity = Audit.velocity system

  component :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex3 F
  component sign mode =
    Helical.helicalProjector E I S sign mode (velocity mode)

  signedEigenvalue :
    Helical.HelicitySign → Z3.FourierMode → C3.Complex F
  signedEigenvalue Helical.plus mode =
    C3.realEmbed F (Helical.modeNorm S mode)
  signedEigenvalue Helical.minus mode =
    C3.realEmbed F (C3.negate F (Helical.modeNorm S mode))

  curlOperatorsAgree :
    (mode : Z3.FourierMode) (value : C3.Complex3 F) →
    Conv.curlFromWave (C3.modeVector E mode) value
    ≡ Helical.curlSymbol E mode value
  curlOperatorsAgree mode value = refl

  componentCurlEigen :
    (sign : Helical.HelicitySign) (mode : Z3.FourierMode) →
    Conv.curlFromWave (C3.modeVector E mode) (component sign mode)
    ≡ C3.complex3Scale
        (signedEigenvalue sign mode)
        (component sign mode)
  componentCurlEigen Helical.plus mode =
    trans
      (curlOperatorsAgree mode (component Helical.plus mode))
      (Helical.helicalCurlEigenvaluePlus L mode (velocity mode))
  componentCurlEigen Helical.minus mode =
    trans
      (curlOperatorsAgree mode (component Helical.minus mode))
      (Helical.helicalCurlEigenvalueMinus L mode (velocity mode))

  componentPairData :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    (signP signQ : Helical.HelicitySign) →
    R106.ProjectedHelicalPairData E I
      (Physical.p tau) (Physical.q tau) (Physical.k tau)
  componentPairData tau outputNonzero signP signQ =
    R106.projected-helical-pair-data
      (Physical.resonance tau)
      outputNonzero
      (component signP (Physical.p tau))
      (component signQ (Physical.q tau))
      (signedEigenvalue signP (Physical.p tau))
      (signedEigenvalue signQ (Physical.q tau))
      (componentCurlEigen signP (Physical.p tau))
      (componentCurlEigen signQ (Physical.q tau))

  multiplierDifferenceVector :
    (tau : Physical.PhysicalTriadIncidence) →
    (signP signQ : Helical.HelicitySign) →
    C3.Complex3 F
  multiplierDifferenceVector tau signP signQ =
    C3.complex3Scale
      (C3.complexSubtract
        (signedEigenvalue signQ (Physical.q tau))
        (signedEigenvalue signP (Physical.p tau)))
      (C3.lerayProject3 E I (Physical.k tau)
        (Cross.complex3Cross
          (component signP (Physical.p tau))
          (component signQ (Physical.q tau))))

  componentPairIsMultiplierDifference :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    pairInteraction E I
      (Physical.k tau) (Physical.p tau) (Physical.q tau)
      (component signP (Physical.p tau))
      (component signQ (Physical.q tau))
    ≡ multiplierDifferenceVector tau signP signQ
  componentPairIsMultiplierDifference tau outputNonzero signP signQ =
    R106.projectedHelicalOrderedPairVector
      (componentPairData tau outputNonzero signP signQ)

  ----------------------------------------------------------------------
  -- 3. Expand one arbitrary raw physical pair into the four sign pairs.
  ----------------------------------------------------------------------

  rawPairExpandsToFourComponents :
    (tau : Physical.PhysicalTriadIncidence) →
    pairInteraction E I
      (Physical.k tau) (Physical.p tau) (Physical.q tau)
      (velocity (Physical.p tau))
      (velocity (Physical.q tau))
    ≡
    C3.complex3Add
      (C3.complex3Add
        (pairInteraction E I
          (Physical.k tau) (Physical.p tau) (Physical.q tau)
          (component Helical.plus (Physical.p tau))
          (component Helical.plus (Physical.q tau)))
        (pairInteraction E I
          (Physical.k tau) (Physical.p tau) (Physical.q tau)
          (component Helical.plus (Physical.p tau))
          (component Helical.minus (Physical.q tau))))
      (C3.complex3Add
        (pairInteraction E I
          (Physical.k tau) (Physical.p tau) (Physical.q tau)
          (component Helical.minus (Physical.p tau))
          (component Helical.plus (Physical.q tau)))
        (pairInteraction E I
          (Physical.k tau) (Physical.p tau) (Physical.q tau)
          (component Helical.minus (Physical.p tau))
          (component Helical.minus (Physical.q tau))))
  rawPairExpandsToFourComponents tau =
    let
      p = Physical.p tau
      q = Physical.q tau
      k = Physical.k tau
      pPlus = component Helical.plus p
      pMinus = component Helical.minus p
      qPlus = component Helical.plus q
      qMinus = component Helical.minus q

      decomposeP : C3.complex3Add pPlus pMinus ≡ velocity p
      decomposeP = Helical.velocityHelicalDecomposition L p (velocity p)
        (velocityTransverse p)

      decomposeQ : C3.complex3Add qPlus qMinus ≡ velocity q
      decomposeQ = Helical.velocityHelicalDecomposition L q (velocity q)
        (velocityTransverse q)
    in
    trans
      (cong₂ (pairInteraction E I k p q)
        (sym decomposeP) (sym decomposeQ))
      (trans
        (pairAddLeft E I k p q pPlus pMinus
          (C3.complex3Add qPlus qMinus))
        (cong₂ C3.complex3Add
          (pairAddRight E I k p q pPlus qPlus qMinus)
          (pairAddRight E I k p q pMinus qPlus qMinus)))

  rawPairIsFourMultiplierDifferences :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    pairInteraction E I
      (Physical.k tau) (Physical.p tau) (Physical.q tau)
      (velocity (Physical.p tau))
      (velocity (Physical.q tau))
    ≡
    C3.complex3Add
      (C3.complex3Add
        (multiplierDifferenceVector tau Helical.plus Helical.plus)
        (multiplierDifferenceVector tau Helical.plus Helical.minus))
      (C3.complex3Add
        (multiplierDifferenceVector tau Helical.minus Helical.plus)
        (multiplierDifferenceVector tau Helical.minus Helical.minus))
  rawPairIsFourMultiplierDifferences tau outputNonzero =
    trans
      (rawPairExpandsToFourComponents tau)
      (cong₂ C3.complex3Add
        (cong₂ C3.complex3Add
          (componentPairIsMultiplierDifference
            tau outputNonzero Helical.plus Helical.plus)
          (componentPairIsMultiplierDifference
            tau outputNonzero Helical.plus Helical.minus))
        (cong₂ C3.complex3Add
          (componentPairIsMultiplierDifference
            tau outputNonzero Helical.minus Helical.plus)
          (componentPairIsMultiplierDifference
            tau outputNonzero Helical.minus Helical.minus)))

  ----------------------------------------------------------------------
  -- 4. Same theorem on R120/R310's actual paired inner-vector carrier.
  ----------------------------------------------------------------------

  partnerVectorSumIsFourMultiplierDifferences :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    R120.partnerVectorSum system tau
    ≡
    C3.complex3Add
      (C3.complex3Add
        (multiplierDifferenceVector tau Helical.plus Helical.plus)
        (multiplierDifferenceVector tau Helical.plus Helical.minus))
      (C3.complex3Add
        (multiplierDifferenceVector tau Helical.minus Helical.plus)
        (multiplierDifferenceVector tau Helical.minus Helical.minus))
  partnerVectorSumIsFourMultiplierDifferences tau outputNonzero =
    trans
      (sym (R111.selfForcingKIsTwoSelectedOrderedTerms system tau))
      (rawPairIsFourMultiplierDifferences tau outputNonzero)

------------------------------------------------------------------------
-- Status / proof-search correction.
------------------------------------------------------------------------

round571RawVelocityRequiredToBeSingleHelicity : Bool
round571RawVelocityRequiredToBeSingleHelicity = false

round571RawInnerPairFourHelicityExpansionClosed : Bool
round571RawInnerPairFourHelicityExpansionClosed = true

round571EachHelicityComponentGetsExactMultiplierDifference : Bool
round571EachHelicityComponentGetsExactMultiplierDifference = true

round571AllInnerHelicalTrajectoryPremiseRequiredForComponentwiseNormalForm : Bool
round571AllInnerHelicalTrajectoryPremiseRequiredForComponentwiseNormalForm = false

round571IntroducesAnyAnalyticEstimate : Bool
round571IntroducesAnyAnalyticEstimate = false

round571SameScaleSummedCommutatorEstimateClosed : Bool
round571SameScaleSummedCommutatorEstimateClosed = false

round571ClayPromotion : Bool
round571ClayPromotion = false

round571RawVelocityRequiredToBeSingleHelicityIsFalse :
  round571RawVelocityRequiredToBeSingleHelicity ≡ false
round571RawVelocityRequiredToBeSingleHelicityIsFalse = refl

round571RawInnerPairFourHelicityExpansionClosedIsTrue :
  round571RawInnerPairFourHelicityExpansionClosed ≡ true
round571RawInnerPairFourHelicityExpansionClosedIsTrue = refl

round571AllInnerHelicalTrajectoryPremiseRequiredForComponentwiseNormalFormIsFalse :
  round571AllInnerHelicalTrajectoryPremiseRequiredForComponentwiseNormalForm ≡ false
round571AllInnerHelicalTrajectoryPremiseRequiredForComponentwiseNormalFormIsFalse = refl

round571ClayPromotionIsFalse : round571ClayPromotion ≡ false
round571ClayPromotionIsFalse = refl
