module DASHI.Physics.Closure.NSTriadKNRawCurlSlotDifferenceOutputPairingRound177Exact where

------------------------------------------------------------------------
-- ROUND177 / RAW p/q CURL AMPLITUDE DIFFERENCE IS A LOW-OUTPUT KERNEL PAIRING
--
-- Round176 factors the vector slotKernel(p,q,u_p,u_q) through the literal
-- output vector k.  This file proves that the actual RAW curl slot difference
-- appearing in Round169--174 is exactly i times that vector kernel under the
-- Hermitian test by u_k.  Hence the second Round174 owner is not merely
-- analogous to the low-output kernel: it IS that same physical object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalWeldRound170Exact as R170
import DASHI.Physics.Closure.NSTriadKNRawCurlOutputDefectFactorizationRound176Exact as R176

rawCurlSlotVectorDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
rawCurlSlotVectorDifference E p q uP uQ =
  C3.complex3Subtract
    (Cross.complex3Cross (Helical.curlSymbol E p uP) uQ)
    (Cross.complex3Cross uP (Helical.curlSymbol E q uQ))

rawCurlSlotVectorDifferenceIsISlotKernel :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  rawCurlSlotVectorDifference E p q uP uQ
  ≡ C3.complex3Scale (C3.complexI F)
      (R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ)
rawCurlSlotVectorDifferenceIsISlotKernel {F = F} E p q uP uQ =
  trans
    (cong₂ C3.complex3Subtract
      (R94.crossScaleLeft (C3.complexI F)
        (Cross.complex3Cross (C3.modeVector E p) uP) uQ)
      (R94.crossScaleRight (C3.complexI F) uP
        (Cross.complex3Cross (C3.modeVector E q) uQ)))
    (R167.complex3ScaleSubtract (C3.complexI F)
      (Cross.complex3Cross
        (Cross.complex3Cross (C3.modeVector E p) uP) uQ)
      (Cross.complex3Cross uP
        (Cross.complex3Cross (C3.modeVector E q) uQ)))

rawCurlPQComplexDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
rawCurlPQComplexDifference E p q uK uP uQ =
  C3.complexSubtract
    (C3.hermitianPairing3 uK
      (Cross.complex3Cross (Helical.curlSymbol E p uP) uQ))
    (C3.hermitianPairing3 uK
      (Cross.complex3Cross uP (Helical.curlSymbol E q uQ)))

rawCurlPQComplexDifferenceIsILowOutputKernelPairing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    (uK uP uQ : C3.Complex3 F) →
  Z3.Resonance p q k →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  rawCurlPQComplexDifference E p q uK uP uQ
  ≡
  C3.complexMultiply (C3.complexI F)
    (C3.hermitianPairing3 uK
      (C3.complex3Subtract
        (C3.complex3Add
          (C3.complex3Scale
            (C3.bilinearDot3 (C3.modeVector E k) uQ) uP)
          (C3.complex3Scale
            (C3.bilinearDot3 uP (C3.modeVector E k)) uQ))
        (C3.complex3Scale
          (C3.bilinearDot3 uP uQ)
          (C3.modeVector E k))))
rawCurlPQComplexDifferenceIsILowOutputKernelPairing {F = F}
    E {p} {q} {k} uK uP uQ resonance pTrans qTrans =
  trans
    (sym
      (Additive.hermitianPairingSubtractRight uK
        (Cross.complex3Cross (Helical.curlSymbol E p uP) uQ)
        (Cross.complex3Cross uP (Helical.curlSymbol E q uQ))))
    (trans
      (cong (C3.hermitianPairing3 uK)
        (rawCurlSlotVectorDifferenceIsISlotKernel E p q uP uQ))
      (trans
        (Scaling.hermitianPairingScaleRight (C3.complexI F) uK
          (R145.slotKernel (C3.modeVector E p) (C3.modeVector E q) uP uQ))
        (cong
          (C3.complexMultiply (C3.complexI F))
          (cong (C3.hermitianPairing3 uK)
            (R176.rawPQSlotKernelFactorsThroughLiteralOutput
              E uP uQ resonance pTrans qTrans)))))

round177RawPQSlotDifferenceSameObjectLowOutputKernel : Bool
round177RawPQSlotDifferenceSameObjectLowOutputKernel = true

round177UsesNormalizedDirectionOrAnglePartition : Bool
round177UsesNormalizedDirectionOrAnglePartition = false

round177CriticalLowOutputKernelL2PaymentClosed : Bool
round177CriticalLowOutputKernelL2PaymentClosed = false

round177PackageAClosed : Bool
round177PackageAClosed = false

round177RawPQSlotDifferenceSameObjectLowOutputKernelIsTrue :
  round177RawPQSlotDifferenceSameObjectLowOutputKernel ≡ true
round177RawPQSlotDifferenceSameObjectLowOutputKernelIsTrue = refl

round177PackageAClosedIsFalse : round177PackageAClosed ≡ false
round177PackageAClosedIsFalse = refl
