{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CyclicHelicalPairingNormalFormRound705Exact where

------------------------------------------------------------------------
-- ROUND705 / MOVE LERAY THROUGH THE ACTUAL HERMITIAN CONSUMER
--
-- R703 exposes one cyclic helical channel vector on the three outer energy
-- presentations.  The R700/R692 scalar consumer is a real Hermitian pairing
-- against a mixed spectator.  Before taking real parts, use exact Leray
-- self-adjointness and Hermitian scale-right linearity:
--
--   <A, c P_k X> = c <P_k A, X>.
--
-- Thus every channel splits into
--
--   scalar eigenvalue difference  *  geometric pairing amplitude.
--
-- For one physical triad beta and mode-attached helicity signs s_p,s_q,s_k,
-- the three complex pairing contributions are
--
--   c_k G_k,   c_p G_p,   c_q G_q,
--
-- with R704 proving c_k - c_p + c_q = 0.
--
-- Consequently exact cyclic cancellation is reduced to the geometric
-- orientation
--
--   G_k = G_q = -G_p.
--
-- This file proves that conditional implication exactly.  It does NOT assume
-- or assert that the R700 spectator rows already satisfy the geometry
-- orientation; that is now the sole exact-cancellation seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness as Leray
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNR650CyclicHelicalVectorTransformRound703Exact as R703
import DASHI.Physics.Closure.NSTriadKNR650CyclicHelicalCoefficientCancellationRound704Exact as R704

module PairingNormalForm
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (velocityReality : Reality.RealityCondition (Audit.velocity system))
    (modeNormEven :
      (mode : Z3.FourierMode) →
      Helical.modeNorm S (Z3.negateMode mode)
      ≡ Helical.modeNorm S mode) where

  module V =
    R703.CyclicChannel
      system S L velocityTransverse velocityReality modeNormEven

  module C =
    R704.OrientedCoefficients
      system S L velocityTransverse

  baseGeometry :
    C3.Complex3 F →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  baseGeometry test beta signP signQ =
    C3.hermitianPairing3
      (C3.lerayProject3 E I (Physical.k beta) test)
      (Cross.complex3Cross
        (V.K.C.component signP (Physical.p beta))
        (V.K.C.component signQ (Physical.q beta)))

  pLegGeometry :
    C3.Complex3 F →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  pLegGeometry test beta signK signQ =
    C3.hermitianPairing3
      (C3.lerayProject3 E I (Physical.p beta) test)
      (Cross.complex3Cross
        (V.K.C.component signK (Physical.k beta))
        (C3.complex3Conjugate
          (V.K.C.component signQ (Physical.q beta))))

  qLegGeometry :
    C3.Complex3 F →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  qLegGeometry test beta signK signP =
    C3.hermitianPairing3
      (C3.lerayProject3 E I (Physical.q beta) test)
      (Cross.complex3Cross
        (V.K.C.component signK (Physical.k beta))
        (C3.complex3Conjugate
          (V.K.C.component signP (Physical.p beta))))

  basePairingFactor :
    (test : C3.Complex3 F) →
    (beta : Physical.PhysicalTriadIncidence) →
    (signP signQ : Helical.HelicitySign) →
    C3.hermitianPairing3 test
      (V.baseChannelVector beta signP signQ)
    ≡
    C3.complexMultiply
      (C.baseCoefficient beta signP signQ)
      (baseGeometry test beta signP signQ)
  basePairingFactor test beta signP signQ =
    trans
      (Scaling.hermitianPairingScaleRight
        (C.baseCoefficient beta signP signQ)
        test
        (C3.lerayProject3 E I (Physical.k beta)
          (Cross.complex3Cross
            (V.K.C.component signP (Physical.p beta))
            (V.K.C.component signQ (Physical.q beta)))))
      (cong
        (C3.complexMultiply (C.baseCoefficient beta signP signQ))
        (sym
          (Leray.leraySelfAdjoint E I (Physical.k beta)
            test
            (Cross.complex3Cross
              (V.K.C.component signP (Physical.p beta))
              (V.K.C.component signQ (Physical.q beta))))))

  pLegPairingFactor :
    (test : C3.Complex3 F) →
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signQ : Helical.HelicitySign) →
    C3.hermitianPairing3 test
      (V.pLegChannelVector beta signK signQ)
    ≡
    C3.complexMultiply
      (C.pLegCoefficient beta signK signQ)
      (pLegGeometry test beta signK signQ)
  pLegPairingFactor test beta signK signQ =
    trans
      (Scaling.hermitianPairingScaleRight
        (C.pLegCoefficient beta signK signQ)
        test
        (C3.lerayProject3 E I (Physical.p beta)
          (Cross.complex3Cross
            (V.K.C.component signK (Physical.k beta))
            (C3.complex3Conjugate
              (V.K.C.component signQ (Physical.q beta))))))
      (cong
        (C3.complexMultiply (C.pLegCoefficient beta signK signQ))
        (sym
          (Leray.leraySelfAdjoint E I (Physical.p beta)
            test
            (Cross.complex3Cross
              (V.K.C.component signK (Physical.k beta))
              (C3.complex3Conjugate
                (V.K.C.component signQ (Physical.q beta)))))))

  qLegPairingFactor :
    (test : C3.Complex3 F) →
    (beta : Physical.PhysicalTriadIncidence) →
    (signK signP : Helical.HelicitySign) →
    C3.hermitianPairing3 test
      (V.qLegChannelVector beta signK signP)
    ≡
    C3.complexMultiply
      (C.qLegCoefficient beta signK signP)
      (qLegGeometry test beta signK signP)
  qLegPairingFactor test beta signK signP =
    trans
      (Scaling.hermitianPairingScaleRight
        (C.qLegCoefficient beta signK signP)
        test
        (C3.lerayProject3 E I (Physical.q beta)
          (Cross.complex3Cross
            (V.K.C.component signK (Physical.k beta))
            (C3.complex3Conjugate
              (V.K.C.component signP (Physical.p beta))))))
      (cong
        (C3.complexMultiply (C.qLegCoefficient beta signK signP))
        (sym
          (Leray.leraySelfAdjoint E I (Physical.q beta)
            test
            (Cross.complex3Cross
              (V.K.C.component signK (Physical.k beta))
              (C3.complex3Conjugate
                (V.K.C.component signP (Physical.p beta)))))))

  cyclicPairing :
    (testK testP testQ : C3.Complex3 F) →
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign →
    Helical.HelicitySign →
    Helical.HelicitySign →
    C3.Complex F
  cyclicPairing testK testP testQ beta signP signQ signK =
    C3.complexAdd
      (C3.complexAdd
        (C3.hermitianPairing3 testK
          (V.baseChannelVector beta signP signQ))
        (C3.hermitianPairing3 testP
          (V.pLegChannelVector beta signK signQ)))
      (C3.hermitianPairing3 testQ
        (V.qLegChannelVector beta signK signP))

  geometryOrientationClosesCyclicPairing :
    (testK testP testQ : C3.Complex3 F) →
    (beta : Physical.PhysicalTriadIncidence) →
    (signP signQ signK : Helical.HelicitySign) →
    let
      G = baseGeometry testK beta signP signQ
    in
    pLegGeometry testP beta signK signQ ≡ C3.complexNegate G →
    qLegGeometry testQ beta signK signP ≡ G →
    cyclicPairing testK testP testQ beta signP signQ signK
      ≡ C3.complexZero F
  geometryOrientationClosesCyclicPairing
      testK testP testQ beta signP signQ signK
      pOrientation qOrientation =
    let
      ck = C.baseCoefficient beta signP signQ
      cp = C.pLegCoefficient beta signK signQ
      cq = C.qLegCoefficient beta signK signP
      G = baseGeometry testK beta signP signQ

      coefficientZero :
        C3.complexAdd
          (C3.complexSubtract ck cp)
          cq
        ≡ C3.complexZero F
      coefficientZero =
        C.orientedCyclicCoefficientZero beta signP signQ signK
    in
    trans
      (cong₂ C3.complexAdd
        (cong₂ C3.complexAdd
          (basePairingFactor testK beta signP signQ)
          (pLegPairingFactor testP beta signK signQ))
        (qLegPairingFactor testQ beta signK signP))
      (trans
        (cong₂ C3.complexAdd
          (cong₂ C3.complexAdd
            refl
            (cong (C3.complexMultiply cp) pOrientation))
          (cong (C3.complexMultiply cq) qOrientation))
        (trans
          (R.solve 4
            (λ ck cp cq g →
              ((ck R.⊗ g)
                R.⊕ (cp R.⊗ (R.⊝ g)))
                R.⊕ (cq R.⊗ g)
              R.⊜
              ((ck R.⊕ (R.⊝ cp)) R.⊕ cq) R.⊗ g)
            refl ck cp cq G)
          (trans
            (cong (λ coefficient → C3.complexMultiply coefficient G)
              coefficientZero)
            (Algebra.complexZeroMultiply F G))))
    where module R = Ring.Solver F

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round705LerayMovedAcrossHermitianConsumerExactly : Bool
round705LerayMovedAcrossHermitianConsumerExactly = true

round705ChannelCoefficientFactoredBeforeRealPart : Bool
round705ChannelCoefficientFactoredBeforeRealPart = true

round705OrientedCoefficientCancellationReducesToGeometryOrientation : Bool
round705OrientedCoefficientCancellationReducesToGeometryOrientation = true

round705RequiredGeometryOrientationClosedOnR700Rows : Bool
round705RequiredGeometryOrientationClosedOnR700Rows = false

round705IntroducesEstimate : Bool
round705IntroducesEstimate = false

round705ClayPromotion : Bool
round705ClayPromotion = false

round705LerayMovedAcrossHermitianConsumerExactlyIsTrue :
  round705LerayMovedAcrossHermitianConsumerExactly ≡ true
round705LerayMovedAcrossHermitianConsumerExactlyIsTrue = refl

round705ChannelCoefficientFactoredBeforeRealPartIsTrue :
  round705ChannelCoefficientFactoredBeforeRealPart ≡ true
round705ChannelCoefficientFactoredBeforeRealPartIsTrue = refl

round705OrientedCoefficientCancellationReducesToGeometryOrientationIsTrue :
  round705OrientedCoefficientCancellationReducesToGeometryOrientation ≡ true
round705OrientedCoefficientCancellationReducesToGeometryOrientationIsTrue = refl

round705RequiredGeometryOrientationClosedOnR700RowsIsFalse :
  round705RequiredGeometryOrientationClosedOnR700Rows ≡ false
round705RequiredGeometryOrientationClosedOnR700RowsIsFalse = refl

round705IntroducesEstimateIsFalse :
  round705IntroducesEstimate ≡ false
round705IntroducesEstimateIsFalse = refl

round705ClayPromotionIsFalse :
  round705ClayPromotion ≡ false
round705ClayPromotionIsFalse = refl
