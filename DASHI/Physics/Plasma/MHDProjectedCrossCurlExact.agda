module DASHI.Physics.Plasma.MHDProjectedCrossCurlExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram as Leray
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Plasma.MHDDoubledInductionProjectedKernelWeldExact as Projected

------------------------------------------------------------------------
-- CROSS OUTPUT IS TRANSVERSE, SO -i P_k[-k x X] IS THE LITERAL CURL SYMBOL.
------------------------------------------------------------------------

crossOrthogonalLeft :
  ∀ {r : Level} {F : C3.RealField r}
    (a b : C3.Complex3 F) →
  C3.bilinearDot3 a (Cross.complex3Cross a b)
  ≡ C3.complexZero F
crossOrthogonalLeft {F = F}
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz) =
  R.solve 6
    (λ ax ay az bx by bz →
      (((ax R.⊗ ((ay R.⊗ bz) R.⊕ (R.⊝ (az R.⊗ by))))
        R.⊕ (ay R.⊗ ((az R.⊗ bx) R.⊕ (R.⊝ (ax R.⊗ bz)))))
        R.⊕ (az R.⊗ ((ax R.⊗ by) R.⊕ (R.⊝ (ay R.⊗ bx)))))
      R.⊜ R.Κ (C3.complexZero F))
    refl ax ay az bx by bz
  where module R = Ring.Solver F

crossOutputTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Helical.Transverse E k
    (Cross.complex3Cross (C3.modeVector E k) value)
crossOutputTransverse E k value =
  crossOrthogonalLeft (C3.modeVector E k) value

minusIMinusCrossIsCurl :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexNegate (C3.complexI F))
    (C3.complex3Negate
      (Cross.complex3Cross (C3.modeVector E k) value))
  ≡ Helical.curlSymbol E k value
minusIMinusCrossIsCurl {F = F} E k
    (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (coordinate
      (C3.x (Cross.complex3Cross (C3.modeVector E k) (C3.complex3 vx vy vz))))
    (coordinate
      (C3.y (Cross.complex3Cross (C3.modeVector E k) (C3.complex3 vx vy vz))))
    (coordinate
      (C3.z (Cross.complex3Cross (C3.modeVector E k) (C3.complex3 vx vy vz))))
  where
  i = C3.complexI F
  coordinate : (c : C3.Complex F) →
    C3.complexMultiply (C3.complexNegate i) (C3.complexNegate c)
    ≡ C3.complexMultiply i c
  coordinate c =
    R.solve 2
      (λ i c → ((R.⊝ i) R.⊗ (R.⊝ c)) R.⊜ (i R.⊗ c))
      refl i c
    where module R = Ring.Solver F

projectedNegativeCrossIsCurl :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Projected.outerProject E I k
    (C3.complex3Negate
      (Cross.complex3Cross (C3.modeVector E k) value))
  ≡ Helical.curlSymbol E k value
projectedNegativeCrossIsCurl {F = F} E I k value =
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (Leray.lerayFixesTransverse E I k
        (C3.complex3Negate
          (Cross.complex3Cross (C3.modeVector E k) value))
        negatedTransverse))
    (minusIMinusCrossIsCurl E k value)
  where
  crossValue = Cross.complex3Cross (C3.modeVector E k) value

  negatedTransverse :
    Helical.Transverse E k (C3.complex3Negate crossValue)
  negatedTransverse =
    trans
      (cong
        (λ v → C3.bilinearDot3 (C3.modeVector E k) v)
        (sym (Additive.complex3ScaleMinusOne crossValue)))
      (trans
        (Scaling.bilinearDot3ScaleRight
          (Additive.minusOne F) (C3.modeVector E k) crossValue)
        (trans
          (cong (C3.complexMultiply (Additive.minusOne F))
            (crossOutputTransverse E k value))
          (Field.complexMultiplyZeroRight (Additive.minusOne F))))

record ProjectedCrossCurlBoundary : Set where
  constructor projected-cross-curl-boundary
  field
    crossOutputTransverseOwned : Bool
    crossOutputTransverseOwnedIsTrue : crossOutputTransverseOwned ≡ true

    lerayDropsFromCrossOutput : Bool
    lerayDropsFromCrossOutputIsTrue : lerayDropsFromCrossOutput ≡ true

    projectedNegativeCrossEqualsCurl : Bool
    projectedNegativeCrossEqualsCurlIsTrue : projectedNegativeCrossEqualsCurl ≡ true

canonicalProjectedCrossCurlBoundary : ProjectedCrossCurlBoundary
canonicalProjectedCrossCurlBoundary =
  projected-cross-curl-boundary true refl true refl true refl
