module DASHI.Physics.Closure.NSTriadKNR571ComponentLowOutputBoundExact where

------------------------------------------------------------------------
-- PERIODIC B / EACH R571 HELICITY COMPONENT HAS THE R326 LOW-OUTPUT BOUND
--
-- R326 proves the radical-free low-output estimate for R120's raw-system
-- helical pair.  R571, however, decomposes an arbitrary transverse physical
-- velocity into four projected helicity-component pairs.  We must not pretend
-- that the raw system velocity itself is single-helicity.
--
-- This owner repeats only the same-object part of R325 one level lower:
-- for EVERY sign pair (s,t),
--
--   M_st
--     = (lambda_t-lambda_s) P_k(u_p^s x u_q^t)
--     = (-i) P_k(rawDirectionalSlotKernel(u_p^s,u_q^t)).
--
-- R178 applies because helical projectors are divergence-free, Leray is
-- norm-contracting, and multiplication by -i preserves squared norm.  Hence
--
--   ||M_st||^2
--     <= 9 |k|^2 ||u_p^s||^2 ||u_q^t||^2
--
-- with no HH hypothesis, midpoint condition, high-leg frequency, or fibre
-- cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as Scalar
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNPureCommutatorRawDualDefectWeldRound325Exact as R325
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571

F : C3.RealField _
F = Rational.rationalRealField

module ComponentBound
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  componentMultiplierDifferenceIsMinusIProjectedRawKernel :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    C.multiplierDifferenceVector tau signP signQ
    ≡
    C3.complex3Scale (R106.minusI F)
      (C3.lerayProject3 E I (Physical.k tau)
        (R172.rawDirectionalSlotKernel
          (C3.modeVector E (Physical.p tau))
          (C3.modeVector E (Physical.q tau))
          (C.component signP (Physical.p tau))
          (C.component signQ (Physical.q tau))))
  componentMultiplierDifferenceIsMinusIProjectedRawKernel
      tau outputNonzero signP signQ =
    let
      p = Physical.p tau
      q = Physical.q tau
      k = Physical.k tau
      uP = C.component signP p
      uQ = C.component signQ q
      X = Cross.complex3Cross uP uQ
      raw = R172.rawDirectionalSlotKernel
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      projectedX = C3.lerayProject3 E I k X
      projectedRaw = C3.lerayProject3 E I k raw
      deltaPQ =
        C3.complexSubtract
          (C.signedEigenvalue signP p)
          (C.signedEigenvalue signQ q)
      deltaQP =
        C3.complexSubtract
          (C.signedEigenvalue signQ q)
          (C.signedEigenvalue signP p)

      D = C.componentPairData tau outputNonzero signP signQ

      rotationalToHelical :
        Conv.rotationalPair
          (C3.modeVector E p) (C3.modeVector E q) uP uQ
        ≡ C3.complex3Scale deltaPQ X
      rotationalToHelical = R106.projectedRotationalHelicalFactor D

      rotationalToRaw :
        Conv.rotationalPair
          (C3.modeVector E p) (C3.modeVector E q) uP uQ
        ≡ C3.complex3Scale (C3.complexI F) raw
      rotationalToRaw =
        R325.R324.rotationalPairIsIRawDirectionalSlotKernel
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
              (C.signedEigenvalue signP p)
              (C.signedEigenvalue signQ q)))

      rightNegate :
        C3.complex3Negate
          (C3.complex3Scale (C3.complexI F) projectedRaw)
        ≡ C3.complex3Scale (R106.minusI F) projectedRaw
      rightNegate =
        R325.complex3NegateScale (C3.complexI F) projectedRaw

      desired :
        C3.complex3Scale deltaQP projectedX
        ≡ C3.complex3Scale (R106.minusI F) projectedRaw
      desired =
        trans
          (sym leftNegate)
          (trans (cong C3.complex3Negate projectedEquality) rightNegate)
    in
    desired

  componentLowOutputBound :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (signP signQ : Helical.HelicitySign) →
    L2.complex3NormSquared
      (C.multiplierDifferenceVector tau signP signQ)
    ≤
    R178.nine * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared
          (C.component signP (Physical.p tau))
      * L2.complex3NormSquared
          (C.component signQ (Physical.q tau))
  componentLowOutputBound tau outputNonzero signP signQ =
    let
      p = Physical.p tau
      q = Physical.q tau
      k = Physical.k tau
      uP = C.component signP p
      uQ = C.component signQ q
      raw = R172.rawDirectionalSlotKernel
        (C3.modeVector E p) (C3.modeVector E q) uP uQ
      projectedRaw = C3.lerayProject3 E I k raw
      target =
        R178.nine * C3.normSquared I k
          * L2.complex3NormSquared uP
          * L2.complex3NormSquared uQ

      rawBound :
        L2.complex3NormSquared raw ≤ target
      rawBound =
        subst
          (λ selected → L2.complex3NormSquared selected ≤ target)
          refl
          (R178.rawLowOutputKernelMassBound
            E I uP uQ (Physical.resonance tau)
            (Helical.helicalProjectorDivergenceFree L signP p
              (Audit.velocity system p))
            (Helical.helicalProjectorDivergenceFree L signQ q
              (Audit.velocity system q)))

      projectedBound :
        L2.complex3NormSquared projectedRaw ≤ target
      projectedBound =
        trans
          (Leray.rationalLerayNormSquaredContraction
            E I O k raw outputNonzero)
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

      sameObject =
        componentMultiplierDifferenceIsMinusIProjectedRawKernel
          tau outputNonzero signP signQ
    in
    subst
      (λ selected → L2.complex3NormSquared selected ≤ target)
      (sym sameObject)
      scaledBound

r571EveryHelicityComponentLowOutputBoundClosed : Bool
r571EveryHelicityComponentLowOutputBoundClosed = true

r571ComponentLowOutputBoundRequiresHH : Bool
r571ComponentLowOutputBoundRequiresHH = false

r571ComponentLowOutputBoundRequiresMidpoint : Bool
r571ComponentLowOutputBoundRequiresMidpoint = false

r571ComponentLowOutputBoundIntroducesHighLegFrequency : Bool
r571ComponentLowOutputBoundIntroducesHighLegFrequency = false

r571ComponentLowOutputBoundIntroducesFibreCardinality : Bool
r571ComponentLowOutputBoundIntroducesFibreCardinality = false

clayPromotion : Bool
clayPromotion = false

r571EveryHelicityComponentLowOutputBoundClosedIsTrue :
  r571EveryHelicityComponentLowOutputBoundClosed ≡ true
r571EveryHelicityComponentLowOutputBoundClosedIsTrue = refl
