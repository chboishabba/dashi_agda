module DASHI.Physics.Plasma.MHDDoubledInductionProjectedKernelWeldExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as Linear
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as LerayLinear
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDDoubledInductionVectorKernelWeldExact as Kernel

------------------------------------------------------------------------
-- SAME-OBJECT WELD: ELSASSER DIFFERENCE -> PROJECTED INDUCTION KERNEL
------------------------------------------------------------------------

private
  two : ∀ {r : Level} {F : C3.RealField r} → C3.Complex F
  two {F = F} = C3.complexAdd (C3.complexOne F) (C3.complexOne F)

  minusI : ∀ {r : Level} (F : C3.RealField r) → C3.Complex F
  minusI F = C3.complexNegate (C3.complexI F)

outerProject :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F
outerProject {F = F} E I k value =
  C3.complex3Scale (minusI F) (C3.lerayProject3 E I k value)

outerProjectScale :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  outerProject E I k (C3.complex3Scale scalar value)
  ≡ C3.complex3Scale scalar (outerProject E I k value)
outerProjectScale {F = F} E I k scalar value =
  trans
    (cong (C3.complex3Scale (minusI F))
      (LerayLinear.lerayProjectComplexScale E I k scalar value))
    (trans
      (LerayLinear.complex3ScaleAssociative
        (minusI F) scalar (C3.lerayProject3 E I k value))
      (trans
        (cong
          (λ coefficient →
            C3.complex3Scale coefficient (C3.lerayProject3 E I k value))
          (Field.complexMultiplyCommutative (minusI F) scalar))
        (sym
          (LerayLinear.complex3ScaleAssociative
            scalar (minusI F) (C3.lerayProject3 E I k value)))))

lerayProjectNegate :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Negate value)
  ≡ C3.complex3Negate (C3.lerayProject3 E I k value)
lerayProjectNegate {F = F} E I k value =
  trans
    (cong (C3.lerayProject3 E I k)
      (sym (Additive.complex3ScaleMinusOne value)))
    (trans
      (LerayLinear.lerayProjectComplexScale
        E I k (Additive.minusOne F) value)
      (Additive.complex3ScaleMinusOne (C3.lerayProject3 E I k value)))

lerayProjectSubtract :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (left right : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Subtract left right)
  ≡ C3.complex3Subtract
      (C3.lerayProject3 E I k left)
      (C3.lerayProject3 E I k right)
lerayProjectSubtract E I k left right =
  trans
    (Linear.lerayProjectAdd E I k left (C3.complex3Negate right))
    (cong
      (C3.complex3Add (C3.lerayProject3 E I k left))
      (lerayProjectNegate E I k right))

outerProjectSubtract :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (left right : C3.Complex3 F) →
  outerProject E I k (C3.complex3Subtract left right)
  ≡ C3.complex3Subtract
      (outerProject E I k left)
      (outerProject E I k right)
outerProjectSubtract {F = F} E I k left right =
  trans
    (cong (C3.complex3Scale (minusI F))
      (lerayProjectSubtract E I k left right))
    (LerayLinear.complex3ScaleSubtract
      (minusI F)
      (C3.lerayProject3 E I k left)
      (C3.lerayProject3 E I k right))

rawPlus :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E)
    (p q : Z3.FourierMode) → C3.Complex3 F
rawPlus E state p q =
  C3.complex3Scale
    (C3.bilinearDot3 (State.zMinus state p) (C3.modeVector E q))
    (State.zPlus state q)

rawMinus :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E)
    (p q : Z3.FourierMode) → C3.Complex3 F
rawMinus E state p q =
  C3.complex3Scale
    (C3.bilinearDot3 (State.zPlus state p) (C3.modeVector E q))
    (State.zMinus state q)

projectedDoubledInductionKernel :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) → C3.Complex3 F
projectedDoubledInductionKernel E I state k p q =
  outerProject E I k
    (Kernel.doubledInductionKernel
      (C3.modeVector E q)
      (State.zPlus state p) (State.zMinus state p)
      (State.zPlus state q) (State.zMinus state q))

doubledElsasserTangentDoublesToProjectedInduction :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) →
  C3.complex3Scale two
    (Doubled.doubledInductionOrderedInteraction I state k p q)
  ≡ projectedDoubledInductionKernel E I state k p q
doubledElsasserTangentDoublesToProjectedInduction {F = F}
    E I state k p q =
  trans
    (LerayLinear.complex3ScaleSubtract two
      (outerProject E I k (rawPlus E state p q))
      (outerProject E I k (rawMinus E state p q)))
    (trans
      (cong₂ C3.complex3Subtract
        (sym (outerProjectScale E I k two (rawPlus E state p q)))
        (sym (outerProjectScale E I k two (rawMinus E state p q))))
      (trans
        (sym
          (outerProjectSubtract E I k
            (C3.complex3Scale two (rawPlus E state p q))
            (C3.complex3Scale two (rawMinus E state p q))))
        (cong (outerProject E I k)
          (trans
            (sym
              (LerayLinear.complex3ScaleSubtract two
                (rawPlus E state p q) (rawMinus E state p q)))
            (Kernel.rawElsasserDifferenceDoublesToVectorInduction
              (C3.modeVector E q)
              (State.zPlus state p) (State.zMinus state p)
              (State.zPlus state q) (State.zMinus state q))))))

record ProjectedInductionKernelWeldBoundary : Set where
  constructor projected-induction-kernel-weld-boundary
  field
    actualElsasserTangentWeldedToInductionKernel : Bool
    actualElsasserTangentWeldedToInductionKernelIsTrue :
      actualElsasserTangentWeldedToInductionKernel ≡ true

    weldUsesDivisionByTwo : Bool
    weldUsesDivisionByTwoIsFalse : weldUsesDivisionByTwo ≡ false

    projectionIntroducesIndependentPhysics : Bool
    projectionIntroducesIndependentPhysicsIsFalse :
      projectionIntroducesIndependentPhysics ≡ false

canonicalProjectedInductionKernelWeldBoundary : ProjectedInductionKernelWeldBoundary
canonicalProjectedInductionKernelWeldBoundary =
  projected-induction-kernel-weld-boundary true refl false refl false refl
