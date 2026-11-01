module DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3NullGainBridge as Null
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
open Audit using (orderedRealityPairCancellation)

------------------------------------------------------------------------
-- The exact tested ordered coefficient after removing Leray from its
-- divergence-free test mode.
------------------------------------------------------------------------

minusI :
  ∀ {r} (F : C3.RealField r) → C3.Complex F
minusI F = C3.complexNegate (C3.complexI F)

orderedTransferNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  Audit.orderedSignedTransferAt E I τ velocity
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (minusI F)
      (C3.complexMultiply
        (C3.bilinearDot3
          (velocity (Physical.p τ))
          (C3.modeVector E (Physical.q τ)))
        (C3.hermitianPairing3
          (velocity (Physical.k τ))
          (velocity (Physical.q τ)))))
orderedTransferNormalForm {F = F} E I τ velocity divergenceFree =
  cong C3.complexRealPart
    (trans
      (Algebra.hermitianScaleRight
        (velocity (Physical.k τ))
        (C3.lerayProject3 E I (Physical.k τ)
          (C3.complex3Scale
            waveFactor
            (velocity (Physical.q τ))))
        (minusI F))
      (cong (C3.complexMultiply (minusI F))
        (trans
          (Algebra.removeLerayFromTransverseTest
            E I
            (Physical.k τ)
            (velocity (Physical.k τ))
            (C3.complex3Scale
              waveFactor
              (velocity (Physical.q τ)))
            (divergenceFree (Physical.k τ)))
          (Algebra.hermitianScaleRight
            (velocity (Physical.k τ))
            (velocity (Physical.q τ))
            waveFactor))))
  where
  waveFactor =
    C3.bilinearDot3
      (velocity (Physical.p τ))
      (C3.modeVector E (Physical.q τ))

------------------------------------------------------------------------
-- Resonance changes the mate wave factor to the literal negative of the
-- original factor.  This is the high-level null identity, now inhabited by
-- the concrete C^3 addition laws.
------------------------------------------------------------------------

complex3LinearCompletion :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  Null.Complex3LinearCompletion F E
complex3LinearCompletion E = record
  { waveVectorAdd = Algebra.modeVectorAdd E
  ; dotAddRight = Algebra.bilinearDotAddRight
  }

mateWaveFactorIsNegative :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  C3.bilinearDot3
    (velocity (Physical.p (Orbit.orderedRealityMate τ)))
    (C3.modeVector E (Physical.q (Orbit.orderedRealityMate τ)))
  ≡
  C3.complexNegate
    (C3.bilinearDot3
      (velocity (Physical.p τ))
      (C3.modeVector E (Physical.q τ)))
mateWaveFactorIsNegative E τ velocity divergenceFree =
  trans
    (cong
      (C3.bilinearDot3 (velocity (Physical.p τ)))
      (C3.modeVectorNegation E (Physical.k τ)))
    (trans
      (Algebra.bilinearDotNegateRight
        (velocity (Physical.p τ))
        (C3.modeVector E (Physical.k τ)))
      (cong C3.complexNegate
        (sym
          (Null.complex3ResonantNullP
            E
            (complex3LinearCompletion E)
            τ
            (velocity (Physical.p τ))
            (divergenceFree (Physical.p τ))))))

matePairingEqualsBasePairing :
  ∀ {r} {F : C3.RealField r}
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  C3.hermitianPairing3
    (velocity (Physical.k (Orbit.orderedRealityMate τ)))
    (velocity (Physical.q (Orbit.orderedRealityMate τ)))
  ≡
  C3.hermitianPairing3
    (velocity (Physical.k τ))
    (velocity (Physical.q τ))
matePairingEqualsBasePairing τ velocity reality =
  trans
    (cong₂ C3.hermitianPairing3
      (reality (Physical.q τ))
      (reality (Physical.k τ)))
    (Algebra.hermitianConjugatePair
      (velocity (Physical.q τ))
      (velocity (Physical.k τ)))

------------------------------------------------------------------------
-- Re(-i z) + Re(-i (-z)) = 0, checked componentwise by the ring normaliser.
------------------------------------------------------------------------

realMinusITwoTermCancellation :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexAdd
    (C3.complexRealPart
      (C3.complexMultiply (minusI F) value))
    (C3.complexRealPart
      (C3.complexMultiply (minusI F) (C3.complexNegate value)))
  ≡ C3.complexZero F
realMinusITwoTermCancellation {F = F} (C3.complex vr vi) =
  Algebra.complexExt
    (P.R.solve 2
      (λ vr vi →
        P.multiplyReal
          (P.R.Κ (C3.zero F)) (P.R.⊝ (P.R.Κ (C3.one F))) vr vi
        P.R.⊕
        P.multiplyReal
          (P.R.Κ (C3.zero F)) (P.R.⊝ (P.R.Κ (C3.one F)))
          (P.R.⊝ vr) (P.R.⊝ vi)
        P.R.⊜ P.R.Κ (C3.zero F))
      refl vr vi)
    (C3.addZeroLeft F (C3.zero F))
  where module P = Algebra.Polynomial F

concreteOrderedRealityPairCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  C3.complexAdd
    (Audit.orderedSignedTransferAt E I τ velocity)
    (Audit.orderedSignedTransferAt E I
      (Orbit.orderedRealityMate τ) velocity)
  ≡ C3.complexZero F
concreteOrderedRealityPairCancellation {F = F}
  E I τ velocity reality divergenceFree =
  trans
    (cong₂ C3.complexAdd
      (orderedTransferNormalForm E I τ velocity divergenceFree)
      (orderedTransferNormalForm
        E I (Orbit.orderedRealityMate τ) velocity divergenceFree))
    (trans
      (cong
        (C3.complexAdd
          (C3.complexRealPart
            (C3.complexMultiply (minusI F) baseProduct)))
        (cong C3.complexRealPart
          (cong (C3.complexMultiply (minusI F))
            (trans
              (cong₂ C3.complexMultiply
                (mateWaveFactorIsNegative E τ velocity divergenceFree)
                (matePairingEqualsBasePairing τ velocity reality))
              (Algebra.complexNegateMultiplyLeft baseWave basePair)))))
      (realMinusITwoTermCancellation baseProduct))
  where
  baseWave =
    C3.bilinearDot3
      (velocity (Physical.p τ))
      (C3.modeVector E (Physical.q τ))
  basePair =
    C3.hermitianPairing3
      (velocity (Physical.k τ))
      (velocity (Physical.q τ))
  baseProduct = C3.complexMultiply baseWave basePair

exactOrderedRealityPairCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (τ : Physical.PhysicalTriadIncidence) →
  Audit.ExactOrderedRealityPairCancellation F E I τ
exactOrderedRealityPairCancellation E I τ = record
  { orderedRealityPairCancellation =
      concreteOrderedRealityPairCancellation E I τ
  }

concreteOrderedRealityPairCancellationClosed : Bool
concreteOrderedRealityPairCancellationClosed = true

concreteOrderedRealityPairCancellationClosedIsTrue :
  concreteOrderedRealityPairCancellationClosed ≡ true
concreteOrderedRealityPairCancellationClosedIsTrue = refl
