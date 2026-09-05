module DASHI.Physics.Plasma.MHDDoubledInductionVectorKernelWeldExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference

------------------------------------------------------------------------
-- EXACT C3 LIFT OF THE DIVISION-FREE INDUCTION NORMAL FORM
------------------------------------------------------------------------

private
  two : ∀ {r : Level} {F : C3.RealField r} → C3.Complex F
  two {F = F} = C3.complexAdd (C3.complexOne F) (C3.complexOne F)

  dot : ∀ {r : Level} {F : C3.RealField r} →
    C3.Complex3 F → C3.Complex3 F → C3.Complex F
  dot = C3.bilinearDot3

  addV : ∀ {r : Level} {F : C3.RealField r} →
    C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
  addV = C3.complex3Add

  subV : ∀ {r : Level} {F : C3.RealField r} →
    C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
  subV = C3.complex3Subtract

  scaleV : ∀ {r : Level} {F : C3.RealField r} →
    C3.Complex F → C3.Complex3 F → C3.Complex3 F
  scaleV = C3.complex3Scale

doubledVelocity :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
doubledVelocity = addV

doubledMagnetic :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
doubledMagnetic = subV

rawElsasserInductionDifference :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
rawElsasserInductionDifference q zPlusP zMinusP zPlusQ zMinusQ =
  subV
    (scaleV (dot zMinusP q) zPlusQ)
    (scaleV (dot zPlusP q) zMinusQ)

doubledInductionKernel :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
doubledInductionKernel q zPlusP zMinusP zPlusQ zMinusQ =
  subV
    (scaleV
      (dot (doubledVelocity zPlusP zMinusP) q)
      (doubledMagnetic zPlusQ zMinusQ))
    (scaleV
      (dot (doubledMagnetic zPlusP zMinusP) q)
      (doubledVelocity zPlusQ zMinusQ))

dotAddLeft :
  ∀ {r : Level} {F : C3.RealField r}
    (u v q : C3.Complex3 F) →
  dot (addV u v) q ≡ C3.complexAdd (dot u q) (dot v q)
dotAddLeft u v q =
  trans
    (Algebra.bilinearDot3Commutative (addV u v) q)
    (trans
      (Algebra.bilinearDot3RightAdd q u v)
      (cong₂ C3.complexAdd
        (Algebra.bilinearDot3Commutative q u)
        (Algebra.bilinearDot3Commutative q v)))

dotSubtractLeft :
  ∀ {r : Level} {F : C3.RealField r}
    (u v q : C3.Complex3 F) →
  dot (subV u v) q ≡ C3.complexSubtract (dot u q) (dot v q)
dotSubtractLeft u v q =
  trans
    (Algebra.bilinearDot3Commutative (subV u v) q)
    (trans
      (Difference.bilinearDot3SubtractRight q u v)
      (cong₂ C3.complexSubtract
        (Algebra.bilinearDot3Commutative q u)
        (Algebra.bilinearDot3Commutative q v)))

coordinateKernelIdentity :
  ∀ {r : Level} {F : C3.RealField r}
    (a b x y : C3.Complex F) →
  C3.complexMultiply two
    (C3.complexSubtract
      (C3.complexMultiply b x)
      (C3.complexMultiply a y))
  ≡
  C3.complexSubtract
    (C3.complexMultiply
      (C3.complexAdd a b)
      (C3.complexSubtract x y))
    (C3.complexMultiply
      (C3.complexSubtract a b)
      (C3.complexAdd x y))
coordinateKernelIdentity {F = F} a b x y =
  R.solve 4
    (λ a b x y →
      (((R.Κ (C3.complexOne F) R.⊕ R.Κ (C3.complexOne F))
        R.⊗ ((b R.⊗ x) R.⊕ (R.⊝ (a R.⊗ y))))
      R.⊜
      ((((a R.⊕ b) R.⊗ (x R.⊕ (R.⊝ y)))
        R.⊕ (R.⊝ ((a R.⊕ (R.⊝ b)) R.⊗ (x R.⊕ y))))))
    refl a b x y
  where module R = Field.Solver F

rawElsasserDifferenceDoublesToVectorInduction :
  ∀ {r : Level} {F : C3.RealField r}
    (q zPlusP zMinusP zPlusQ zMinusQ : C3.Complex3 F) →
  scaleV two
    (rawElsasserInductionDifference q zPlusP zMinusP zPlusQ zMinusQ)
  ≡ doubledInductionKernel q zPlusP zMinusP zPlusQ zMinusQ
rawElsasserDifferenceDoublesToVectorInduction
    q zPlusP zMinusP
    (C3.complex3 zpQx zpQy zpQz)
    (C3.complex3 zmQx zmQy zmQz)
  rewrite dotAddLeft zPlusP zMinusP q
        | dotSubtractLeft zPlusP zMinusP q =
  Field.complex3Ext
    (coordinateKernelIdentity
      (dot zPlusP q) (dot zMinusP q) zpQx zmQx)
    (coordinateKernelIdentity
      (dot zPlusP q) (dot zMinusP q) zpQy zmQy)
    (coordinateKernelIdentity
      (dot zPlusP q) (dot zMinusP q) zpQz zmQz)

record DoubledInductionVectorWeldBoundary : Set where
  constructor doubled-induction-vector-weld-boundary
  field
    vectorKernelWeldOwned : Bool
    vectorKernelWeldOwnedIsTrue : vectorKernelWeldOwned ≡ true

    outerProjectionOrMinusIChangesKernelIdentity : Bool
    outerProjectionOrMinusIChangesKernelIdentityIsFalse :
      outerProjectionOrMinusIChangesKernelIdentity ≡ false

    vectorKernelWeldAloneClosesThreeLegHelicity : Bool
    vectorKernelWeldAloneClosesThreeLegHelicityIsFalse :
      vectorKernelWeldAloneClosesThreeLegHelicity ≡ false

canonicalDoubledInductionVectorWeldBoundary : DoubledInductionVectorWeldBoundary
canonicalDoubledInductionVectorWeldBoundary =
  doubled-induction-vector-weld-boundary true refl false refl false refl
