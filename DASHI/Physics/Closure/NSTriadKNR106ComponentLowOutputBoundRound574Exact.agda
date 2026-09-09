module DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact where

------------------------------------------------------------------------
-- ROUND574 / R106 HELICAL COMPONENT PAIR -> RADICAL-FREE LOW-OUTPUT BOUND
--
-- R325/R326 prove the low-output estimate through R120's raw-system helical
-- packaging.  Their algebraic proof, however, only uses the R106 helical pair
-- data plus the universal R178 transverse raw-kernel estimate.
--
-- This owner removes that packaging restriction.  For ANY R106
-- ProjectedHelicalPairData on the rational physical carrier,
--
--   M = (lambda_q-lambda_p) P_k(u_p x u_q)
--
-- is exactly
--
--   M = (-i) P_k(rawDirectionalSlotKernel(p,q,u_p,u_q)),
--
-- and hence for resonant transverse inputs
--
--   ||M||^2 <= 9 |k|^2 ||u_p||^2 ||u_q||^2.
--
-- Instantiating this with R571's projected +/- components proves the same bound
-- for ALL FOUR helical sign channels of an arbitrary physical velocity pair.
-- There is no high-leg frequency and no convolution-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as Scalar
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNRotationalPairRawDirectionalRound324Exact as R324
import DASHI.Physics.Closure.NSTriadKNPureCommutatorRawDualDefectWeldRound325Exact as R325
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571

F : C3.RealField _
F = DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField

r106MultiplierDifferenceVector :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k : Z3.FourierMode} →
  R106.ProjectedHelicalPairData E I p q k → C3.Complex3 F
r106MultiplierDifferenceVector {E} {I} {k = k} H =
  C3.complex3Scale
    (C3.complexSubtract (R106.signedEigenQ H) (R106.signedEigenP H))
    (C3.lerayProject3 E I k
      (Cross.complex3Cross (R106.uP H) (R106.uQ H)))

r106MultiplierDifferenceIsMinusIProjectedRawKernel :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k : Z3.FourierMode}
    (H : R106.ProjectedHelicalPairData E I p q k) →
  r106MultiplierDifferenceVector H
  ≡
  C3.complex3Scale (R106.minusI F)
    (C3.lerayProject3 E I k
      (R172.rawDirectionalSlotKernel
        (C3.modeVector E p) (C3.modeVector E q)
        (R106.uP H) (R106.uQ H)))
r106MultiplierDifferenceIsMinusIProjectedRawKernel
    {E} {I} {p} {q} {k} H =
  let
    uP = R106.uP H
    uQ = R106.uQ H
    X = Cross.complex3Cross uP uQ
    raw = R172.rawDirectionalSlotKernel
      (C3.modeVector E p) (C3.modeVector E q) uP uQ
    deltaPQ = C3.complexSubtract
      (R106.signedEigenP H) (R106.signedEigenQ H)
    deltaQP = C3.complexSubtract
      (R106.signedEigenQ H) (R106.signedEigenP H)
    projectedX = C3.lerayProject3 E I k X
    projectedRaw = C3.lerayProject3 E I k raw

    rotationalToHelical :
      Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      ≡ C3.complex3Scale deltaPQ X
    rotationalToHelical = R106.projectedRotationalHelicalFactor H

    rotationalToRaw :
      Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      ≡ C3.complex3Scale (C3.complexI F) raw
    rotationalToRaw =
      R324.rotationalPairIsIRawDirectionalSlotKernel
        (C3.modeVector E p) (C3.modeVector E q) uP uQ

    helicalEqualsRaw :
      C3.complex3Scale deltaPQ X
      ≡ C3.complex3Scale (C3.complexI F) raw
    helicalEqualsRaw = trans (sym rotationalToHelical) rotationalToRaw

    projectedEquality :
      C3.complex3Scale deltaPQ projectedX
      ≡ C3.complex3Scale (C3.complexI F) projectedRaw
    projectedEquality =
      trans
        (sym (Scalar.lerayProjectComplexScale E I k deltaPQ X))
        (trans
          (cong (C3.lerayProject3 E I k) helicalEqualsRaw)
          (Scalar.lerayProjectComplexScale E I k (C3.complexI F) raw))

    leftNegate :
      C3.complex3Negate (C3.complex3Scale deltaPQ projectedX)
      ≡ C3.complex3Scale deltaQP projectedX
    leftNegate =
      trans
        (R325.complex3NegateScale deltaPQ projectedX)
        (cong
          (λ scalar → C3.complex3Scale scalar projectedX)
          (R106.negateSubtractSwap
            (R106.signedEigenP H) (R106.signedEigenQ H)))

    rightNegate :
      C3.complex3Negate
        (C3.complex3Scale (C3.complexI F) projectedRaw)
      ≡ C3.complex3Scale (R106.minusI F) projectedRaw
    rightNegate = R325.complex3NegateScale (C3.complexI F) projectedRaw
  in
  trans
    (sym leftNegate)
    (trans (cong C3.complex3Negate projectedEquality) rightNegate)

r106MultiplierDifferenceLowOutputBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    {p q k : Z3.FourierMode}
    (H : R106.ProjectedHelicalPairData E I p q k) →
  Helical.Transverse E p (R106.uP H) →
  Helical.Transverse E q (R106.uQ H) →
  L2.complex3NormSquared (r106MultiplierDifferenceVector H)
  ≤ R178.nine * C3.normSquared I k
      * L2.complex3NormSquared (R106.uP H)
      * L2.complex3NormSquared (R106.uQ H)
r106MultiplierDifferenceLowOutputBound {E} {I} O {p} {q} {k}
    H pTrans qTrans =
  let
    uP = R106.uP H
    uQ = R106.uQ H
    raw = R172.rawDirectionalSlotKernel
      (C3.modeVector E p) (C3.modeVector E q) uP uQ
    projectedRaw = C3.lerayProject3 E I k raw
    target = R178.nine * C3.normSquared I k
      * L2.complex3NormSquared uP
      * L2.complex3NormSquared uQ

    rawBound : L2.complex3NormSquared raw ≤ target
    rawBound =
      subst
        (λ selected → L2.complex3NormSquared selected ≤ target)
        (sym (R326.rawKernelAgreement
          (C3.modeVector E p) (C3.modeVector E q) uP uQ))
        (R178.rawLowOutputKernelMassBound
          E I uP uQ (R106.resonance H) pTrans qTrans)

    projectedBound : L2.complex3NormSquared projectedRaw ≤ target
    projectedBound =
      ℚP.≤-trans
        (Leray.rationalLerayNormSquaredContraction
          E I O k raw (R106.outputNonzero H))
        rawBound

    scaledBound :
      L2.complex3NormSquared
        (C3.complex3Scale (R106.minusI F) projectedRaw)
      ≤ target
    scaledBound =
      subst
        (λ lower → lower ≤ target)
        (sym (R326.minusIScalePreservesNormSquared projectedRaw))
        projectedBound
  in
  subst
    (λ selected → L2.complex3NormSquared selected ≤ target)
    (sym (r106MultiplierDifferenceIsMinusIProjectedRawKernel H))
    scaledBound

------------------------------------------------------------------------
-- Physical arbitrary-velocity component instantiation.
------------------------------------------------------------------------

module PhysicalComponents
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  componentLowOutputBound :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    L2.complex3NormSquared
      (C.multiplierDifferenceVector tau signP signQ)
    ≤ R178.nine * C3.normSquared I (Physical.k tau)
        * L2.complex3NormSquared
            (C.component signP (Physical.p tau))
        * L2.complex3NormSquared
            (C.component signQ (Physical.q tau))
  componentLowOutputBound tau outputNonzero signP signQ =
    let
      H = C.componentPairData tau outputNonzero signP signQ
      pTrans = Helical.helicalProjectorDivergenceFree
        L signP (Physical.p tau) (Audit.velocity system (Physical.p tau))
      qTrans = Helical.helicalProjectorDivergenceFree
        L signQ (Physical.q tau) (Audit.velocity system (Physical.q tau))
    in
    r106MultiplierDifferenceLowOutputBound O H pTrans qTrans

------------------------------------------------------------------------
-- Status correction.
------------------------------------------------------------------------

round574R325IdentityGeneralizedToArbitraryR106Pair : Bool
round574R325IdentityGeneralizedToArbitraryR106Pair = true

round574AllFourPhysicalHelicalComponentsHaveLowOutputBound : Bool
round574AllFourPhysicalHelicalComponentsHaveLowOutputBound = true

round574HighLegFrequencyAppearsInComponentBound : Bool
round574HighLegFrequencyAppearsInComponentBound = false

round574FibreCardinalityFactorAppearsInComponentBound : Bool
round574FibreCardinalityFactorAppearsInComponentBound = false

round574RawVelocitySingleHelicityRequired : Bool
round574RawVelocitySingleHelicityRequired = false

round574InnerFibreSummedBoundClosed : Bool
round574InnerFibreSummedBoundClosed = false

round574OuterWeightedSpacetimeBoundClosed : Bool
round574OuterWeightedSpacetimeBoundClosed = false

round574ClayPromotion : Bool
round574ClayPromotion = false

round574AllFourPhysicalHelicalComponentsHaveLowOutputBoundIsTrue :
  round574AllFourPhysicalHelicalComponentsHaveLowOutputBound ≡ true
round574AllFourPhysicalHelicalComponentsHaveLowOutputBoundIsTrue = refl

round574RawVelocitySingleHelicityRequiredIsFalse :
  round574RawVelocitySingleHelicityRequired ≡ false
round574RawVelocitySingleHelicityRequiredIsFalse = refl

round574ClayPromotionIsFalse : round574ClayPromotion ≡ false
round574ClayPromotionIsFalse = refl
