module DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceQuadraticPairingRound168Exact where

------------------------------------------------------------------------
-- ROUND168 / CUBIC SLOT DIFFERENCE = LINEAR TEST AGAINST QUADRATIC KERNEL
--
-- Round167 identifies the vector difference in the p/q normalized-curl slots
-- as i times the quadratic anti-parallel kernel.  This module moves that exact
-- identity through the Hermitian pairing:
--
--   B_p - B_q = i <u_k , K_{p,q}(u_p,u_q)>.
--
-- Thus the surviving cubic channel is explicitly a linear factor times a
-- quadratic companion.  This is the amplitude-degree-4 companion surface
-- demanded by Round166/Round156, without introducing |B_p-B_q|^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167

slotPComplexAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
slotPComplexAmplitude E S p uK uP uQ =
  C3.hermitianPairing3 uK
    (Cross.complex3Cross (R142.normalizedCurl E S p uP) uQ)

slotQComplexAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex F
slotQComplexAmplitude E S q uK uP uQ =
  C3.hermitianPairing3 uK
    (Cross.complex3Cross uP (R142.normalizedCurl E S q uQ))

quadraticKernelPairing :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
quadraticKernelPairing E S p q uK uP uQ =
  C3.hermitianPairing3 uK
    (R145.slotKernel
      (R167.normalizedDirection E S p)
      (R167.normalizedDirection E S q)
      uP uQ)

slotPQComplexDifferenceIsIQuadraticKernelPairing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  C3.complexSubtract
    (slotPComplexAmplitude E S p uK uP uQ)
    (slotQComplexAmplitude E S q uK uP uQ)
  ≡ C3.complexMultiply (C3.complexI F)
      (quadraticKernelPairing E S p q uK uP uQ)
slotPQComplexDifferenceIsIQuadraticKernelPairing {F = F}
    E S p q uK uP uQ =
  trans
    (sym
      (Additive.hermitianPairingSubtractRight uK
        (Cross.complex3Cross (R142.normalizedCurl E S p uP) uQ)
        (Cross.complex3Cross uP (R142.normalizedCurl E S q uQ))))
    (trans
      (cong (C3.hermitianPairing3 uK)
        (R167.normalizedCurlSlotVectorDifferenceIsIQuadraticKernel
          E S p q uP uQ))
      (Scaling.hermitianPairingScaleRight
        (C3.complexI F) uK
        (R145.slotKernel
          (R167.normalizedDirection E S p)
          (R167.normalizedDirection E S q)
          uP uQ)))

slotPQRealDifferenceIsRealIQuadraticKernelPairing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  C3.complexRealPart
    (C3.complexSubtract
      (slotPComplexAmplitude E S p uK uP uQ)
      (slotQComplexAmplitude E S q uK uP uQ))
  ≡ C3.complexRealPart
      (C3.complexMultiply (C3.complexI F)
        (quadraticKernelPairing E S p q uK uP uQ))
slotPQRealDifferenceIsRealIQuadraticKernelPairing E S p q uK uP uQ =
  cong C3.complexRealPart
    (slotPQComplexDifferenceIsIQuadraticKernelPairing E S p q uK uP uQ)

round168SlotDifferenceQuadraticPairingClosed : Bool
round168SlotDifferenceQuadraticPairingClosed = true

round168RawCubicDefectEnergyUsedAsCompanion : Bool
round168RawCubicDefectEnergyUsedAsCompanion = false

round168QuadraticKernelGlobalL2BudgetClosed : Bool
round168QuadraticKernelGlobalL2BudgetClosed = false

round168PackageAClosed : Bool
round168PackageAClosed = false

round168SlotDifferenceQuadraticPairingClosedIsTrue :
  round168SlotDifferenceQuadraticPairingClosed ≡ true
round168SlotDifferenceQuadraticPairingClosedIsTrue = refl

round168PackageAClosedIsFalse : round168PackageAClosed ≡ false
round168PackageAClosedIsFalse = refl
