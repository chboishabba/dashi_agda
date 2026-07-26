module DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered
import DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly as Assembly

open Assembly.OrderedTransferCancellationLaws
open Audit.ExactTriadEnergyCancellation

------------------------------------------------------------------------
-- Reality conjugates the two scalar factors in the ordered normal form and
-- contributes two minus signs (one from the wavevector, one from -i).  The
-- real part is therefore invariant on the conjugate lattice triad.
------------------------------------------------------------------------

conjugateWaveFactor :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  C3.bilinearDot3
    (velocity (Physical.p (Symmetry.conjugateTriad τ)))
    (C3.modeVector E (Physical.q (Symmetry.conjugateTriad τ)))
  ≡
  C3.complexNegate
    (C3.complexConjugate
      (C3.bilinearDot3
        (velocity (Physical.p τ))
        (C3.modeVector E (Physical.q τ))))
conjugateWaveFactor E τ velocity reality =
  trans
    (cong₂ C3.bilinearDot3
      (reality (Physical.p τ))
      (C3.modeVectorNegation E (Physical.q τ)))
    (trans
      (Algebra.bilinearDotNegateRight
        (C3.complex3Conjugate (velocity (Physical.p τ)))
        (C3.modeVector E (Physical.q τ)))
      (cong C3.complexNegate
        (trans
          (cong
            (C3.bilinearDot3
              (C3.complex3Conjugate (velocity (Physical.p τ))))
            (sym (C3.modeVectorConjugate E (Physical.q τ))))
          (Algebra.bilinearDotConjugate
            (velocity (Physical.p τ))
            (C3.modeVector E (Physical.q τ))))))

conjugatePairing :
  ∀ {r} {F : C3.RealField r}
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  C3.hermitianPairing3
    (velocity (Physical.k (Symmetry.conjugateTriad τ)))
    (velocity (Physical.q (Symmetry.conjugateTriad τ)))
  ≡
  C3.complexConjugate
    (C3.hermitianPairing3
      (velocity (Physical.k τ))
      (velocity (Physical.q τ)))
conjugatePairing τ velocity reality =
  trans
    (cong₂ C3.hermitianPairing3
      (reality (Physical.k τ))
      (reality (Physical.q τ)))
    (trans
      (Algebra.hermitianConjugatePair
        (velocity (Physical.k τ))
        (velocity (Physical.q τ)))
      (Algebra.hermitianConjugateSymmetry
        (velocity (Physical.k τ))
        (velocity (Physical.q τ))))

conjugateNormalFormInvariant :
  ∀ {r} {F : C3.RealField r}
    (wave pairing : C3.Complex F) →
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply
        (C3.complexNegate (C3.complexConjugate wave))
        (C3.complexConjugate pairing)))
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply wave pairing))
conjugateNormalFormInvariant {F = F}
  (C3.complex wr wi) (C3.complex pr pi) =
  Algebra.complexExt
    (P.R.solve 4
      (λ wr wi pr pi →
        P.multiplyReal
          (P.R.Κ (C3.zero F)) (P.R.⊝ (P.R.Κ (C3.one F)))
          (P.multiplyReal
            (P.R.⊝ wr) wi
            pr (P.R.⊝ pi))
          (P.multiplyImaginary
            (P.R.⊝ wr) wi
            pr (P.R.⊝ pi))
        P.R.⊜
        P.multiplyReal
          (P.R.Κ (C3.zero F)) (P.R.⊝ (P.R.Κ (C3.one F)))
          (P.multiplyReal wr wi pr pi)
          (P.multiplyImaginary wr wi pr pi))
      refl wr wi pr pi)
    refl
  where module P = Algebra.Polynomial F

orderedTransferConjugateInvariant :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (τ : Physical.PhysicalTriadIncidence) →
  Audit.orderedSignedTransferAt E I
    (Symmetry.conjugateTriad τ) velocity
  ≡ Audit.orderedSignedTransferAt E I τ velocity
orderedTransferConjugateInvariant {F = F}
  E I velocity reality divergenceFree τ =
  trans
    (Ordered.orderedTransferNormalForm
      E I (Symmetry.conjugateTriad τ) velocity divergenceFree)
    (trans
      (cong C3.complexRealPart
        (cong (C3.complexMultiply (Ordered.minusI F))
          (cong₂ C3.complexMultiply
            (conjugateWaveFactor E τ velocity reality)
            (conjugatePairing τ velocity reality))))
      (trans
        (conjugateNormalFormInvariant baseWave basePair)
        (sym (Ordered.orderedTransferNormalForm
          E I τ velocity divergenceFree))))
  where
  baseWave =
    C3.bilinearDot3
      (velocity (Physical.p τ))
      (C3.modeVector E (Physical.q τ))
  basePair =
    C3.hermitianPairing3
      (velocity (Physical.k τ))
      (velocity (Physical.q τ))

orderedTransferRespectsLattice :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    {left right : Physical.PhysicalTriadIncidence} →
  Symmetry.SameLatticeTriad left right →
  Audit.orderedSignedTransferAt E I left velocity
  ≡ Audit.orderedSignedTransferAt E I right velocity
orderedTransferRespectsLattice E I velocity
  (Symmetry.same-lattice-triad refl refl refl) = refl

concreteOrderedTransferLaws :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  Assembly.OrderedTransferCancellationLaws (C3.Complex F)
concreteOrderedTransferLaws {F = F}
  E I velocity reality divergenceFree = record
  { zero = C3.complexZero F
  ; add = C3.complexAdd
  ; addZeroLeft = Algebra.complexAddZeroLeft
  ; addZeroRight = Algebra.complexAddZeroRight
  ; reorderSix = Algebra.complexAddReorderSix
  ; orderedTransfer = λ τ →
      Audit.orderedSignedTransferAt E I τ velocity
  ; respectsLattice = orderedTransferRespectsLattice E I velocity
  ; conjugateInvariant =
      orderedTransferConjugateInvariant
        E I velocity reality divergenceFree
  ; orderedRealityMateCancels = λ τ →
      Ordered.concreteOrderedRealityPairCancellation
        E I τ velocity reality divergenceFree
  }

------------------------------------------------------------------------
-- The ordered-pair coefficient is definitionally the sum of the two ordered
-- placements after Hermitian and real-part additivity are exposed.
------------------------------------------------------------------------

orderedPairCoefficientIsOrderedSum :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (τ : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.orderedPairSignedTransferAt E I τ velocity
  ≡
  C3.complexAdd
    (Audit.orderedSignedTransferAt E I τ velocity)
    (Audit.orderedSignedTransferAt E I
      (Symmetry.swapTriad τ) velocity)
orderedPairCoefficientIsOrderedSum {F = F} E I τ velocity =
  trans
    (cong C3.complexRealPart
      (Algebra.hermitianAddRight
        (velocity (Physical.k τ))
        firstInteraction
        secondInteraction))
    (Algebra.complexRealPartAdd
      (C3.hermitianPairing3
        (velocity (Physical.k τ)) firstInteraction)
      (C3.hermitianPairing3
        (velocity (Physical.k τ)) secondInteraction))
  where
  laws = C3.complex3VelocityGalerkinLaws F E I
  firstInteraction =
    Signed.orderedVelocityInteraction laws
      (Physical.k τ) (Physical.p τ) (Physical.q τ)
      (velocity (Physical.p τ)) (velocity (Physical.q τ))
  secondInteraction =
    Signed.orderedVelocityInteraction laws
      (Physical.k τ) (Physical.q τ) (Physical.p τ)
      (velocity (Physical.q τ)) (velocity (Physical.p τ))

exactTriadEnergyCancellation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (τ : Physical.PhysicalTriadIncidence) →
  Audit.ExactTriadEnergyCancellation F E I τ
exactTriadEnergyCancellation E I τ = record
  { completeTriadCancellation =
      λ velocity reality divergenceFree →
        trans
          (cong₂ C3.complexAdd
            (cong₂ C3.complexAdd
              (orderedPairCoefficientIsOrderedSum E I τ velocity)
              (orderedPairCoefficientIsOrderedSum
                E I (Orbit.pEnergyLeg τ) velocity))
            (orderedPairCoefficientIsOrderedSum
              E I (Orbit.qEnergyLeg τ) velocity))
          (Assembly.orderedRealityCancellationImpliesThreeLegCancellation
            (concreteOrderedTransferLaws
              E I velocity reality divergenceFree)
            τ)
  }

concreteThreeLegEnergyCancellationClosed : Bool
concreteThreeLegEnergyCancellationClosed = true

concreteThreeLegEnergyCancellationClosedIsTrue :
  concreteThreeLegEnergyCancellationClosed ≡ true
concreteThreeLegEnergyCancellationClosedIsTrue = refl
