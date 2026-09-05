module DASHI.Physics.Plasma.MHDOrderedPairInductionCurlWeldExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as Linear
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as LerayLinear
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact as Doubled
import DASHI.Physics.Plasma.MHDDoubledInductionVectorKernelWeldExact as Kernel
import DASHI.Physics.Plasma.MHDDoubledInductionProjectedKernelWeldExact as Projected
import DASHI.Physics.Plasma.MHDOrderedPairInductionCurlBidiExact as CurlPair
import DASHI.Physics.Plasma.MHDProjectedCrossCurlExact as CrossCurl

------------------------------------------------------------------------
-- ACTUAL ORDERED-PAIR DOUBLED INDUCTION TANGENT = CURL-CROSS NORMAL FORM
------------------------------------------------------------------------

private
  two : ∀ {r : Level} {F : C3.RealField r} → C3.Complex F
  two {F = F} = C3.complexAdd (C3.complexOne F) (C3.complexOne F)

orderedPairDoubledInduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  State.IdealElsasserFourierState F E →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
orderedPairDoubledInduction I state tau =
  C3.complex3Add
    (Doubled.doubledInductionOrderedInteraction I state
      (Physical.k tau) (Physical.p tau) (Physical.q tau))
    (Doubled.doubledInductionOrderedInteraction I state
      (Physical.k tau) (Physical.q tau) (Physical.p tau))

kernelAt :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
kernelAt E state tau =
  Kernel.doubledInductionKernel
    (C3.modeVector E (Physical.q tau))
    (State.zPlus state (Physical.p tau))
    (State.zMinus state (Physical.p tau))
    (State.zPlus state (Physical.q tau))
    (State.zMinus state (Physical.q tau))

kernelAtIsPhysicalKernel :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  kernelAt E state tau
  ≡ CurlPair.inductionKernel
      (C3.modeVector E (Physical.q tau))
      (CurlPair.doubledVelocity state (Physical.p tau))
      (Doubled.doubledMagnetic state (Physical.p tau))
      (CurlPair.doubledVelocity state (Physical.q tau))
      (Doubled.doubledMagnetic state (Physical.q tau))
kernelAtIsPhysicalKernel E state tau = refl

outerProjectAdd :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Physical.PhysicalTriadIncidence)
    (left right : C3.Complex3 F) →
  Projected.outerProject E I (Physical.k k) (C3.complex3Add left right)
  ≡ C3.complex3Add
      (Projected.outerProject E I (Physical.k k) left)
      (Projected.outerProject E I (Physical.k k) right)
outerProjectAdd {F = F} E I tau left right =
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (Linear.lerayProjectAdd E I (Physical.k tau) left right))
    (LerayLinear.complex3ScaleAdd
      (C3.complexNegate (C3.complexI F))
      (C3.lerayProject3 E I (Physical.k tau) left)
      (C3.lerayProject3 E I (Physical.k tau) right))

orderedPairDoubledInductionDoublesToProjectedKernelPair :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complex3Scale two (orderedPairDoubledInduction I state tau)
  ≡ Projected.outerProject E I (Physical.k tau)
      (C3.complex3Add (kernelAt E state tau)
        (kernelAt E state (Symmetry.swapTriad tau)))
orderedPairDoubledInductionDoublesToProjectedKernelPair E I state tau =
  trans
    (LerayLinear.complex3ScaleAdd two
      (Doubled.doubledInductionOrderedInteraction I state
        (Physical.k tau) (Physical.p tau) (Physical.q tau))
      (Doubled.doubledInductionOrderedInteraction I state
        (Physical.k tau) (Physical.q tau) (Physical.p tau)))
    (trans
      (cong₂ C3.complex3Add
        (Projected.doubledElsasserTangentDoublesToProjectedInduction
          E I state (Physical.k tau) (Physical.p tau) (Physical.q tau))
        (Projected.doubledElsasserTangentDoublesToProjectedInduction
          E I state (Physical.k tau) (Physical.q tau) (Physical.p tau)))
      (sym
        (outerProjectAdd E I tau
          (kernelAt E state tau)
          (kernelAt E state (Symmetry.swapTriad tau)))))

orderedPairDoubledInductionDoublesToCurlCrosses :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (tau : Physical.PhysicalTriadIncidence) →
  C3.complex3Scale two (orderedPairDoubledInduction I state tau)
  ≡
  C3.complex3Add
    (Helical.curlSymbol E (Physical.k tau)
      (Cross.complex3Cross
        (CurlPair.doubledVelocity state (Physical.p tau))
        (Doubled.doubledMagnetic state (Physical.q tau))))
    (Helical.curlSymbol E (Physical.k tau)
      (Cross.complex3Cross
        (CurlPair.doubledVelocity state (Physical.q tau))
        (Doubled.doubledMagnetic state (Physical.p tau))))
orderedPairDoubledInductionDoublesToCurlCrosses E I state tau =
  trans
    (orderedPairDoubledInductionDoublesToProjectedKernelPair E I state tau)
    (trans
      (cong (Projected.outerProject E I (Physical.k tau))
        (trans
          (cong₂ C3.complex3Add
            (kernelAtIsPhysicalKernel E state tau)
            (kernelAtIsPhysicalKernel E state (Symmetry.swapTriad tau)))
          (CurlPair.physicalOrderedPairKernelIsTwoNegativeCurlCrosses E state tau)))
      (trans
        (outerProjectAdd E I tau
          (C3.complex3Negate
            (Cross.complex3Cross
              (C3.modeVector E (Physical.k tau))
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.p tau))
                (Doubled.doubledMagnetic state (Physical.q tau)))))
          (C3.complex3Negate
            (Cross.complex3Cross
              (C3.modeVector E (Physical.k tau))
              (Cross.complex3Cross
                (CurlPair.doubledVelocity state (Physical.q tau))
                (Doubled.doubledMagnetic state (Physical.p tau))))))
        (cong₂ C3.complex3Add
          (CrossCurl.projectedNegativeCrossIsCurl E I (Physical.k tau)
            (Cross.complex3Cross
              (CurlPair.doubledVelocity state (Physical.p tau))
              (Doubled.doubledMagnetic state (Physical.q tau))))
          (CrossCurl.projectedNegativeCrossIsCurl E I (Physical.k tau)
            (Cross.complex3Cross
              (CurlPair.doubledVelocity state (Physical.q tau))
              (Doubled.doubledMagnetic state (Physical.p tau)))))))

record OrderedPairInductionCurlWeldBoundary : Set where
  constructor ordered-pair-induction-curl-weld-boundary
  field
    actualDoubledTangentWeldOwned : Bool
    actualDoubledTangentWeldOwnedIsTrue : actualDoubledTangentWeldOwned ≡ true

    orderedPairRequiredForCurlNormalForm : Bool
    orderedPairRequiredForCurlNormalFormIsTrue :
      orderedPairRequiredForCurlNormalForm ≡ true

    divisionByTwoUsed : Bool
    divisionByTwoUsedIsFalse : divisionByTwoUsed ≡ false

canonicalOrderedPairInductionCurlWeldBoundary : OrderedPairInductionCurlWeldBoundary
canonicalOrderedPairInductionCurlWeldBoundary =
  ordered-pair-induction-curl-weld-boundary true refl true refl false refl
