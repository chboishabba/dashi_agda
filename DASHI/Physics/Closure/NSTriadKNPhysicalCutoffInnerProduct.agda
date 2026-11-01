module DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNFiniteCoordinateAlgebraCore as Finite
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffCoordinateVectors as Coordinates
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffModeSupport as Support
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Sector
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorAssembly as Gram
import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNStage3NegativeTransferContrast as Contrast

------------------------------------------------------------------------
-- Exact finite-coordinate Euclidean algebra for the physical cutoff carrier.
--
-- `ExactOrderedScalar` deliberately stopped at the coefficient-order facts.
-- This extension states precisely the additive and distributive laws needed
-- to prove finite coordinate identities.  It is separate so the symbolic
-- coefficient lane does not accidentally acquire an unproved field model.
------------------------------------------------------------------------

record ExactOrderedCommutativeRing : Set₁ where
  constructor mkExactOrderedCommutativeRing
  field
    orderedScalar : Scalar.ExactOrderedScalar

    addAssociative :
      (a b c : Scalar.Scalar orderedScalar) →
      Scalar._+_ orderedScalar (Scalar._+_ orderedScalar a b) c ≡
      Scalar._+_ orderedScalar a (Scalar._+_ orderedScalar b c)
    addCommutative :
      (a b : Scalar.Scalar orderedScalar) →
      Scalar._+_ orderedScalar a b ≡ Scalar._+_ orderedScalar b a
    addZeroLeft :
      (a : Scalar.Scalar orderedScalar) →
      Scalar._+_ orderedScalar (Scalar.zero orderedScalar) a ≡ a
    addInverseLeft :
      (a : Scalar.Scalar orderedScalar) →
      Scalar._+_ orderedScalar (Scalar.neg orderedScalar a) a ≡
      Scalar.zero orderedScalar
    negDistributesOverAddition :
      (a b : Scalar.Scalar orderedScalar) →
      Scalar.neg orderedScalar (Scalar._+_ orderedScalar a b) ≡
      Scalar._+_ orderedScalar
        (Scalar.neg orderedScalar a) (Scalar.neg orderedScalar b)

    mulAssociative :
      (a b c : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar (Scalar._*_ orderedScalar a b) c ≡
      Scalar._*_ orderedScalar a (Scalar._*_ orderedScalar b c)
    mulCommutative :
      (a b : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar a b ≡ Scalar._*_ orderedScalar b a
    mulOneLeft :
      (a : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar (Scalar.one orderedScalar) a ≡ a
    mulZeroLeft :
      (a : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar (Scalar.zero orderedScalar) a ≡
      Scalar.zero orderedScalar
    mulDistributesOverAdditionRight :
      (a b c : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar a (Scalar._+_ orderedScalar b c) ≡
      Scalar._+_ orderedScalar
        (Scalar._*_ orderedScalar a b)
        (Scalar._*_ orderedScalar a c)
    negMultiplicationLeft :
      (a b : Scalar.Scalar orderedScalar) →
      Scalar._*_ orderedScalar (Scalar.neg orderedScalar a) b ≡
      Scalar.neg orderedScalar (Scalar._*_ orderedScalar a b)

open ExactOrderedCommutativeRing public

sumFin :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  (Fin n → Scalar.Scalar S) → Scalar.Scalar S
sumFin S {zero} f = Scalar.zero S
sumFin S {suc n} f =
  Scalar._+_ S (f zero) (sumFin S (λ i → f (suc i)))

sumFinCong :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  {f g : Fin n → Scalar.Scalar S} →
  ((i : Fin n) → f i ≡ g i) →
  sumFin S f ≡ sumFin S g
sumFinCong S {zero} pointwise = refl
sumFinCong S {suc n} {f} {g} pointwise =
  cong₂ (Scalar._+_ S) (pointwise zero)
    (sumFinCong S (λ i → pointwise (suc i)))

addZeroRight :
  (K : ExactOrderedCommutativeRing) →
  (a : Scalar.Scalar (orderedScalar K)) →
  Scalar._+_ (orderedScalar K) a (Scalar.zero (orderedScalar K)) ≡ a
addZeroRight K a =
  trans (addCommutative K a (Scalar.zero (orderedScalar K)))
    (addZeroLeft K a)

mulZeroRight :
  (K : ExactOrderedCommutativeRing) →
  (a : Scalar.Scalar (orderedScalar K)) →
  Scalar._*_ (orderedScalar K) a (Scalar.zero (orderedScalar K)) ≡
  Scalar.zero (orderedScalar K)
mulZeroRight K a =
  trans (mulCommutative K a (Scalar.zero (orderedScalar K)))
    (mulZeroLeft K a)

negZero :
  (K : ExactOrderedCommutativeRing) →
  Scalar.neg (orderedScalar K) (Scalar.zero (orderedScalar K)) ≡
  Scalar.zero (orderedScalar K)
negZero K =
  trans
    (sym (addZeroRight K (Scalar.neg (orderedScalar K) (Scalar.zero (orderedScalar K)))) )
    (addInverseLeft K (Scalar.zero (orderedScalar K)))

addFourShuffle :
  (K : ExactOrderedCommutativeRing) →
  (a b c d : Scalar.Scalar (orderedScalar K)) →
  Scalar._+_ (orderedScalar K)
    (Scalar._+_ (orderedScalar K) a b)
    (Scalar._+_ (orderedScalar K) c d) ≡
  Scalar._+_ (orderedScalar K)
    (Scalar._+_ (orderedScalar K) a c)
    (Scalar._+_ (orderedScalar K) b d)
addFourShuffle K a b c d =
  trans
    (addAssociative K a b (Scalar._+_ (orderedScalar K) c d))
    (trans
      (cong (Scalar._+_ (orderedScalar K) a)
        (sym (addAssociative K b c d)))
      (trans
        (cong (Scalar._+_ (orderedScalar K) a)
          (cong (λ q → Scalar._+_ (orderedScalar K) q d)
            (addCommutative K b c)))
        (trans
          (cong (Scalar._+_ (orderedScalar K) a)
            (addAssociative K c b d))
          (sym (addAssociative K a c
            (Scalar._+_ (orderedScalar K) b d))))))

sumFinAdd :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (f g : Fin n → Scalar.Scalar (orderedScalar K)) →
  sumFin (orderedScalar K)
    (λ i → Scalar._+_ (orderedScalar K) (f i) (g i)) ≡
  Scalar._+_ (orderedScalar K)
    (sumFin (orderedScalar K) f)
    (sumFin (orderedScalar K) g)
sumFinAdd K {zero} f g = sym (addZeroLeft K (Scalar.zero (orderedScalar K)))
sumFinAdd K {suc n} f g =
  trans
    (cong (Scalar._+_ (orderedScalar K)
      (Scalar._+_ (orderedScalar K) (f zero) (g zero)))
      (sumFinAdd K (λ i → f (suc i)) (λ i → g (suc i))))
    (addFourShuffle K (f zero) (g zero)
      (sumFin (orderedScalar K) (λ i → f (suc i)))
      (sumFin (orderedScalar K) (λ i → g (suc i))))

sumFinNeg :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (f : Fin n → Scalar.Scalar (orderedScalar K)) →
  sumFin (orderedScalar K)
    (λ i → Scalar.neg (orderedScalar K) (f i)) ≡
  Scalar.neg (orderedScalar K) (sumFin (orderedScalar K) f)
sumFinNeg K {zero} f = sym (negZero K)
sumFinNeg K {suc n} f =
  trans
    (cong (Scalar._+_ (orderedScalar K)
      (Scalar.neg (orderedScalar K) (f zero)))
      (sumFinNeg K (λ i → f (suc i))))
    (sym (negDistributesOverAddition K (f zero)
      (sumFin (orderedScalar K) (λ i → f (suc i)))))

mulDistributesOverAdditionLeft :
  (K : ExactOrderedCommutativeRing) →
  (a b c : Scalar.Scalar (orderedScalar K)) →
  Scalar._*_ (orderedScalar K)
    (Scalar._+_ (orderedScalar K) a b) c ≡
  Scalar._+_ (orderedScalar K)
    (Scalar._*_ (orderedScalar K) a c)
    (Scalar._*_ (orderedScalar K) b c)
mulDistributesOverAdditionLeft K a b c =
  trans
    (mulCommutative K (Scalar._+_ (orderedScalar K) a b) c)
    (trans
      (mulDistributesOverAdditionRight K c a b)
      (cong₂ (Scalar._+_ (orderedScalar K))
        (mulCommutative K c a)
        (mulCommutative K c b)))

sumFinAllZero :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  sumFin (orderedScalar K) (λ (_ : Fin n) → Scalar.zero (orderedScalar K)) ≡
  Scalar.zero (orderedScalar K)
sumFinAllZero K {zero} = refl
sumFinAllZero K {suc n} =
  trans
    (cong (Scalar._+_ (orderedScalar K) (Scalar.zero (orderedScalar K)))
      (sumFinAllZero K {n}))
    (addZeroLeft K (Scalar.zero (orderedScalar K)))

sumFinMulLeft :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (a : Scalar.Scalar (orderedScalar K)) →
  (f : Fin n → Scalar.Scalar (orderedScalar K)) →
  sumFin (orderedScalar K) (λ i → Scalar._*_ (orderedScalar K) a (f i)) ≡
  Scalar._*_ (orderedScalar K) a (sumFin (orderedScalar K) f)
sumFinMulLeft K {zero} a f = sym (mulZeroRight K a)
sumFinMulLeft K {suc n} a f =
  trans
    (cong (Scalar._+_ (orderedScalar K)
      (Scalar._*_ (orderedScalar K) a (f zero)))
      (sumFinMulLeft K a (λ i → f (suc i))))
    (sym (mulDistributesOverAdditionRight K a (f zero)
      (sumFin (orderedScalar K) (λ i → f (suc i)))))

innerFin :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  (Fin n → Scalar.Scalar S) → (Fin n → Scalar.Scalar S) → Scalar.Scalar S
innerFin S x y = sumFin S (λ i → Scalar._*_ S (x i) (y i))

innerFinSymmetric :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (x y : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x y ≡ innerFin (orderedScalar K) y x
innerFinSymmetric K x y =
  sumFinCong (orderedScalar K)
    (λ i → mulCommutative K (x i) (y i))

rankOneQuadraticGeneric :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (coefficient : Scalar.Scalar (orderedScalar K)) →
  (b z : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) z
    (λ i → Scalar._*_ (orderedScalar K)
      (Scalar._*_ (orderedScalar K) coefficient
        (innerFin (orderedScalar K) b z))
      (b i)) ≡
  Scalar._*_ (orderedScalar K) coefficient
    (Scalar._*_ (orderedScalar K)
      (innerFin (orderedScalar K) b z)
      (innerFin (orderedScalar K) b z))
rankOneQuadraticGeneric K coefficient b z =
  trans
    (sumFinCong (orderedScalar K)
      (λ i →
        trans
          (sym (mulAssociative K (z i)
            (Scalar._*_ (orderedScalar K) coefficient
              (innerFin (orderedScalar K) b z)) (b i)))
          (trans
            (cong (λ q → Scalar._*_ (orderedScalar K) q (b i))
              (mulCommutative K (z i)
                (Scalar._*_ (orderedScalar K) coefficient
                  (innerFin (orderedScalar K) b z))))
            (mulAssociative K
              (Scalar._*_ (orderedScalar K) coefficient
                (innerFin (orderedScalar K) b z))
              (z i) (b i)))))
    (trans
      (sumFinMulLeft K
        (Scalar._*_ (orderedScalar K) coefficient
          (innerFin (orderedScalar K) b z))
        (λ i → Scalar._*_ (orderedScalar K) (z i) (b i)))
      (trans
        (cong
          (Scalar._*_ (orderedScalar K)
            (Scalar._*_ (orderedScalar K) coefficient
              (innerFin (orderedScalar K) b z)))
          (innerFinSymmetric K z b))
        (mulAssociative K coefficient
          (innerFin (orderedScalar K) b z)
          (innerFin (orderedScalar K) b z))))

coordinateBasisInner :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (i : Fin n) → (z : Fin n → Scalar.Scalar (orderedScalar K)) →
  sumFin (orderedScalar K)
    (λ j → Scalar._*_ (orderedScalar K) (Finite.coordinateBasis (orderedScalar K) i j) (z j)) ≡
  z i
coordinateBasisInner K {zero} () z
coordinateBasisInner K {suc n} zero z =
  trans
    (cong (Scalar._+_ (orderedScalar K)
      (Scalar._*_ (orderedScalar K) (Scalar.one (orderedScalar K)) (z zero)))
      (trans
        (sumFinCong (orderedScalar K)
          (λ j → mulZeroLeft K (z (suc j))))
        (sumFinAllZero K {n = n})))
    (trans
      (addZeroRight K
        (Scalar._*_ (orderedScalar K) (Scalar.one (orderedScalar K)) (z zero)))
      (mulOneLeft K (z zero)))
coordinateBasisInner K {suc n} (suc i) z =
  trans
    (cong (Scalar._+_ (orderedScalar K)
      (Scalar._*_ (orderedScalar K) (Scalar.zero (orderedScalar K)) (z zero)))
      (coordinateBasisInner K i (λ j → z (suc j))))
    (trans
      (cong (λ q → Scalar._+_ (orderedScalar K) q (z (suc i)))
        (mulZeroLeft K (z zero)))
      (addZeroLeft K (z (suc i))) )

coordinateBasisDifferenceInner :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (i j : Fin n) → (z : Fin n → Scalar.Scalar (orderedScalar K)) →
  sumFin (orderedScalar K)
    (λ q → Scalar._*_ (orderedScalar K)
      (Scalar._+_ (orderedScalar K)
        (Finite.coordinateBasis (orderedScalar K) i q)
        (Scalar.neg (orderedScalar K)
          (Finite.coordinateBasis (orderedScalar K) j q)))
      (z q)) ≡
  Scalar._+_ (orderedScalar K) (z i)
    (Scalar.neg (orderedScalar K) (z j))
coordinateBasisDifferenceInner K i j z =
  trans
    (sumFinCong (orderedScalar K)
      (λ q → mulDistributesOverAdditionLeft K
        (Finite.coordinateBasis (orderedScalar K) i q)
        (Scalar.neg (orderedScalar K)
          (Finite.coordinateBasis (orderedScalar K) j q))
        (z q)))
    (trans
      (sumFinAdd K
        (λ q → Scalar._*_ (orderedScalar K)
          (Finite.coordinateBasis (orderedScalar K) i q) (z q))
        (λ q → Scalar._*_ (orderedScalar K)
          (Scalar.neg (orderedScalar K)
            (Finite.coordinateBasis (orderedScalar K) j q)) (z q)))
      (trans
        (cong (Scalar._+_ (orderedScalar K)
          (sumFin (orderedScalar K)
            (λ q → Scalar._*_ (orderedScalar K)
              (Finite.coordinateBasis (orderedScalar K) i q) (z q))))
          (trans
            (sumFinCong (orderedScalar K)
              (λ q → negMultiplicationLeft K
                (Finite.coordinateBasis (orderedScalar K) j q) (z q)))
            (sumFinNeg K
              (λ q → Scalar._*_ (orderedScalar K)
                (Finite.coordinateBasis (orderedScalar K) j q) (z q)))))
        (cong₂ (Scalar._+_ (orderedScalar K))
          (coordinateBasisInner K i z)
          (cong (Scalar.neg (orderedScalar K))
            (coordinateBasisInner K j z)))))

physicalCutoffInner :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  Coordinates.PhysicalCutoffVector S N R sector →
  Coordinates.PhysicalCutoffVector S N R sector →
  Scalar.Scalar S
physicalCutoffInner S {N} {R} {sector} x y =
  sumFin S (λ i → Scalar._*_ S (x i) (y i))

square :
  (S : Scalar.ExactOrderedScalar) →
  Scalar.Scalar S → Scalar.Scalar S
square S x = Scalar._*_ S x x

rankOneAction :
  (S : Scalar.ExactOrderedScalar) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  Scalar.Scalar S →
  Coordinates.PhysicalCutoffVector S N R sector →
  Coordinates.PhysicalCutoffVector S N R sector →
  Coordinates.PhysicalCutoffVector S N R sector
rankOneAction S {N} {R} {sector} coefficient b z i =
  Scalar._*_ S
    (Scalar._*_ S coefficient (physicalCutoffInner S {N} {R} {sector} b z))
    (b i)

-- This is the concrete vector fixed by the physical incidence convention.
-- It is intentionally defined on the membership-indexed incidence carrier:
-- every endpoint coordinate is consequently total on the same finite shell.
physicalIncidenceVector :
  (S : Scalar.ExactOrderedScalar) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  Support.PhysicalCutoffIncidence N R sector →
  Coordinates.PhysicalCutoffVector S N R sector
physicalIncidenceVector = Coordinates.physicalPairIncidenceVector

-- The canonical basis used by the Euclidean-algebra lane.  The dimension is
-- written explicitly here, so its finite-coordinate proofs do not need to
-- reduce the shell/cutoff enumeration itself.
canonicalPhysicalBasisVector :
  (S : Scalar.ExactOrderedScalar) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  Support.physicalCutoffModeCoordinate N R sector →
  Coordinates.PhysicalCutoffVector S N R sector
canonicalPhysicalBasisVector S N R sector =
  Finite.coordinateBasis S
    {n = length (Support.physicalCutoffNormalizedModeSupport N R sector)}

------------------------------------------------------------------------
-- Fail-closed concrete algebra targets.
--
-- These are theorem types, not fields of the Gram assembly.  An inhabitant
-- must be derived from `ExactOrderedCommutativeRing` by finite-sum induction;
-- no coefficient, profile, or Fourier-dynamics premise can discharge them.
------------------------------------------------------------------------

BasisInnerProductTarget :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (i : Support.physicalCutoffModeCoordinate N R sector) →
  (z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  Set
BasisInnerProductTarget K {N} {R} {sector} i z =
  physicalCutoffInner (orderedScalar K) {N} {R} {sector}
    (canonicalPhysicalBasisVector (orderedScalar K) N R sector i) z ≡ z i

physicalBasisInnerProduct :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (i : Support.physicalCutoffModeCoordinate N R sector) →
  (z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  BasisInnerProductTarget K {N} {R} {sector} i z
physicalBasisInnerProduct K {N} {R} {sector} i z =
  coordinateBasisInner K
    {n = length (Support.physicalCutoffNormalizedModeSupport N R sector)}
    i z

PhysicalIncidenceEvaluationTarget :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (r : Support.PhysicalCutoffIncidence N R sector) →
  (z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  Set
PhysicalIncidenceEvaluationTarget K {N} {R} {sector} r z =
  physicalCutoffInner (orderedScalar K) {N} {R} {sector}
    (physicalIncidenceVector (orderedScalar K) N R sector r) z ≡
  Scalar._+_ (orderedScalar K)
    (z (Support.sourceCoordinate N R sector r))
    (Scalar.neg (orderedScalar K)
      (z (Support.targetCoordinate N R sector r)))

physicalIncidenceEvaluation :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (r : Support.PhysicalCutoffIncidence N R sector) →
  (z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  PhysicalIncidenceEvaluationTarget K {N} {R} {sector} r z
physicalIncidenceEvaluation K {N} {R} {sector} r z =
  coordinateBasisDifferenceInner K
    {n = length (Support.physicalCutoffNormalizedModeSupport N R sector)}
    (Support.sourceCoordinate N R sector r)
    (Support.targetCoordinate N R sector r)
    z

RankOneQuadraticIdentityTarget :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (coefficient : Scalar.Scalar (orderedScalar K)) →
  (b z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  Set
RankOneQuadraticIdentityTarget K {N} {R} {sector} coefficient b z =
  physicalCutoffInner (orderedScalar K) {N} {R} {sector} z
    (rankOneAction (orderedScalar K) {N} {R} {sector} coefficient b z) ≡
  Scalar._*_ (orderedScalar K) coefficient
    (square (orderedScalar K)
      (physicalCutoffInner (orderedScalar K) {N} {R} {sector} b z))

physicalRankOneQuadraticIdentity :
  (K : ExactOrderedCommutativeRing) →
  {N R : Nat} {sector : Sector.ExactOutputRetainedSectorLaw N R} →
  (coefficient : Scalar.Scalar (orderedScalar K)) →
  (b z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  RankOneQuadraticIdentityTarget K {N} {R} {sector} coefficient b z
physicalRankOneQuadraticIdentity K {N} {R} {sector} coefficient b z =
  rankOneQuadraticGeneric K
    {n = length (Support.physicalCutoffNormalizedModeSupport N R sector)}
    coefficient b z

------------------------------------------------------------------------
-- Concrete finite rank-one folds.
--
-- These lemmas discharge the linear-algebra fields of the finite
-- inner-product interface for the actual cutoff coordinate carrier.
-- They are polymorphic only in the finite list being folded; the vector
-- carrier remains exactly Fin n -> Scalar.
------------------------------------------------------------------------

pointwiseScale :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  Scalar.Scalar S → (Fin n → Scalar.Scalar S) →
  Fin n → Scalar.Scalar S
pointwiseScale S coefficient x i = Scalar._*_ S coefficient (x i)

innerFinZeroRight :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (x : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x (λ _ → Scalar.zero (orderedScalar K)) ≡
  Scalar.zero (orderedScalar K)
innerFinZeroRight K {n} x =
  trans
    (sumFinCong (orderedScalar K)
      (λ i → mulZeroRight K (x i)))
    (sumFinAllZero K {n = n})

innerFinAddRight :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (x y z : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x
    (λ i → Scalar._+_ (orderedScalar K) (y i) (z i)) ≡
  Scalar._+_ (orderedScalar K)
    (innerFin (orderedScalar K) x y)
    (innerFin (orderedScalar K) x z)
innerFinAddRight K x y z =
  trans
    (sumFinCong (orderedScalar K)
      (λ i → mulDistributesOverAdditionRight K (x i) (y i) (z i)))
    (sumFinAdd K
      (λ i → Scalar._*_ (orderedScalar K) (x i) (y i))
      (λ i → Scalar._*_ (orderedScalar K) (x i) (z i)))

innerFinAddLeft :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (x y z : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K)
    (λ i → Scalar._+_ (orderedScalar K) (x i) (y i)) z ≡
  Scalar._+_ (orderedScalar K)
    (innerFin (orderedScalar K) x z)
    (innerFin (orderedScalar K) y z)
innerFinAddLeft K x y z =
  trans
    (innerFinSymmetric K
      (λ i → Scalar._+_ (orderedScalar K) (x i) (y i)) z)
    (trans
      (innerFinAddRight K z x y)
      (cong₂ (Scalar._+_ (orderedScalar K))
        (innerFinSymmetric K z x)
        (innerFinSymmetric K z y)))

rankOneBilinearNormalForm :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (coefficient : Scalar.Scalar (orderedScalar K)) →
  (b x y : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x
    (pointwiseScale (orderedScalar K)
      (Scalar._*_ (orderedScalar K) coefficient
        (innerFin (orderedScalar K) b y)) b) ≡
  Scalar._*_ (orderedScalar K) coefficient
    (Scalar._*_ (orderedScalar K)
      (innerFin (orderedScalar K) b x)
      (innerFin (orderedScalar K) b y))
rankOneBilinearNormalForm K coefficient b x y =
  trans
    (sumFinCong (orderedScalar K)
      (λ i →
        trans
          (sym (mulAssociative K (x i)
            (Scalar._*_ (orderedScalar K) coefficient
              (innerFin (orderedScalar K) b y)) (b i)))
          (trans
            (cong (λ q → Scalar._*_ (orderedScalar K) q (b i))
              (mulCommutative K (x i)
                (Scalar._*_ (orderedScalar K) coefficient
                  (innerFin (orderedScalar K) b y))))
            (mulAssociative K
              (Scalar._*_ (orderedScalar K) coefficient
                (innerFin (orderedScalar K) b y))
              (x i) (b i)))))
    (trans
      (sumFinMulLeft K
        (Scalar._*_ (orderedScalar K) coefficient
          (innerFin (orderedScalar K) b y))
        (λ i → Scalar._*_ (orderedScalar K) (x i) (b i)))
      (trans
        (cong
          (Scalar._*_ (orderedScalar K)
            (Scalar._*_ (orderedScalar K) coefficient
              (innerFin (orderedScalar K) b y)))
          (innerFinSymmetric K x b))
        (trans
          (mulAssociative K coefficient
            (innerFin (orderedScalar K) b y)
            (innerFin (orderedScalar K) b x))
          (cong (Scalar._*_ (orderedScalar K) coefficient)
            (mulCommutative K
              (innerFin (orderedScalar K) b y)
              (innerFin (orderedScalar K) b x))))))

rankOneBilinearSelfAdjoint :
  (K : ExactOrderedCommutativeRing) → {n : Nat} →
  (coefficient : Scalar.Scalar (orderedScalar K)) →
  (b x y : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x
    (pointwiseScale (orderedScalar K)
      (Scalar._*_ (orderedScalar K) coefficient
        (innerFin (orderedScalar K) b y)) b) ≡
  innerFin (orderedScalar K)
    (pointwiseScale (orderedScalar K)
      (Scalar._*_ (orderedScalar K) coefficient
        (innerFin (orderedScalar K) b x)) b) y
rankOneBilinearSelfAdjoint K coefficient b x y =
  trans
    (rankOneBilinearNormalForm K coefficient b x y)
    (trans
      (cong (Scalar._*_ (orderedScalar K) coefficient)
        (mulCommutative K
          (innerFin (orderedScalar K) b x)
          (innerFin (orderedScalar K) b y)))
      (sym
        (trans
          (innerFinSymmetric K
            (pointwiseScale (orderedScalar K)
              (Scalar._*_ (orderedScalar K) coefficient
                (innerFin (orderedScalar K) b x)) b) y)
          (rankOneBilinearNormalForm K coefficient b y x))))

rankOneFold :
  (K : ExactOrderedCommutativeRing) → {n : Nat} {A : Set} →
  (A → Scalar.Scalar (orderedScalar K)) →
  (A → Fin n → Scalar.Scalar (orderedScalar K)) →
  List A → (Fin n → Scalar.Scalar (orderedScalar K)) →
  Fin n → Scalar.Scalar (orderedScalar K)
rankOneFold K coefficient b [] z i = Scalar.zero (orderedScalar K)
rankOneFold K coefficient b (a ∷ as) z i =
  Scalar._+_ (orderedScalar K)
    (pointwiseScale (orderedScalar K)
      (Scalar._*_ (orderedScalar K) (coefficient a)
        (innerFin (orderedScalar K) (b a) z))
      (b a) i)
    (rankOneFold K coefficient b as z i)

rankOneFoldQuadraticExpansion :
  (K : ExactOrderedCommutativeRing) → {n : Nat} {A : Set} →
  (coefficient : A → Scalar.Scalar (orderedScalar K)) →
  (b : A → Fin n → Scalar.Scalar (orderedScalar K)) →
  (xs : List A) → (z : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) z (rankOneFold K coefficient b xs z) ≡
  Exact.weightedListSum
    {S = Scalar.exactScalarOperations (orderedScalar K)}
    (λ a → Scalar._*_ (orderedScalar K) (coefficient a)
      (square (orderedScalar K) (innerFin (orderedScalar K) (b a) z)))
    xs
rankOneFoldQuadraticExpansion K coefficient b [] z =
  trans (innerFinZeroRight K z) refl
rankOneFoldQuadraticExpansion K coefficient b (a ∷ as) z =
  trans
    (innerFinAddRight K z
      (pointwiseScale (orderedScalar K)
        (Scalar._*_ (orderedScalar K) (coefficient a)
          (innerFin (orderedScalar K) (b a) z))
        (b a))
      (rankOneFold K coefficient b as z))
    (cong₂ (Scalar._+_ (orderedScalar K))
      (rankOneQuadraticGeneric K (coefficient a) (b a) z)
      (rankOneFoldQuadraticExpansion K coefficient b as z))

rankOneFoldSelfAdjoint :
  (K : ExactOrderedCommutativeRing) → {n : Nat} {A : Set} →
  (coefficient : A → Scalar.Scalar (orderedScalar K)) →
  (b : A → Fin n → Scalar.Scalar (orderedScalar K)) →
  (xs : List A) → (x y : Fin n → Scalar.Scalar (orderedScalar K)) →
  innerFin (orderedScalar K) x (rankOneFold K coefficient b xs y) ≡
  innerFin (orderedScalar K) (rankOneFold K coefficient b xs x) y
rankOneFoldSelfAdjoint K coefficient b [] x y =
  trans
    (innerFinZeroRight K x)
    (sym
      (trans
        (innerFinSymmetric K
          (λ _ → Scalar.zero (orderedScalar K)) y)
        (innerFinZeroRight K y)))
rankOneFoldSelfAdjoint K coefficient b (a ∷ as) x y =
  trans
    (innerFinAddRight K x
      (pointwiseScale (orderedScalar K)
        (Scalar._*_ (orderedScalar K) (coefficient a)
          (innerFin (orderedScalar K) (b a) y))
        (b a))
      (rankOneFold K coefficient b as y))
    (trans
      (cong₂ (Scalar._+_ (orderedScalar K))
        (rankOneBilinearSelfAdjoint K (coefficient a) (b a) x y)
        (rankOneFoldSelfAdjoint K coefficient b as x y))
      (sym
        (innerFinAddLeft K
          (pointwiseScale (orderedScalar K)
            (Scalar._*_ (orderedScalar K) (coefficient a)
              (innerFin (orderedScalar K) (b a) x))
            (b a))
          (rankOneFold K coefficient b as x) y)))

physicalCutoffFiniteShellInnerProductSpace :
  (K : ExactOrderedCommutativeRing) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  Gram.FiniteShellInnerProductSpace
    (Scalar.exactScalarOperations (orderedScalar K))
physicalCutoffFiniteShellInnerProductSpace K N R sector =
  record
    { Vector = Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector
    ; zeroVector = Coordinates.zeroVector (orderedScalar K) N R sector
    ; _+ᵥ_ = λ x y →
        Coordinates.pointwiseAdd (orderedScalar K)
          {N} {R} {sector} x y
    ; _•_ = λ coefficient x →
        pointwiseScale (orderedScalar K)
          {n = length (Support.physicalCutoffNormalizedModeSupport N R sector)}
          coefficient x
    ; inner = λ x y →
        physicalCutoffInner (orderedScalar K) {N} {R} {sector} x y
    ; innerZeroRight = innerFinZeroRight K
    ; innerAddRight = innerFinAddRight K
    ; rankOneQuadraticFormula = rankOneQuadraticGeneric K
    ; rankOneSum = rankOneFold K
    ; rankOneSumQuadraticFormula = rankOneFoldQuadraticExpansion K
    ; rankOneSumSelfAdjoint = rankOneFoldSelfAdjoint K
    }

-- This is the canonical physical cutoff Gram datum.  Both the incidence
-- list and its coordinate vectors use membership-indexed incidences, so no
-- endpoint is re-indexed through an unrelated occurrence list.
canonicalPhysicalCutoffNegativeTransferContrastData :
  (K : ExactOrderedCommutativeRing) →
  (C : Fourier.ComplexFourierInterface (orderedScalar K)) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  {interaction :
    Fourier.PhysicalTriadInteractionLaw (orderedScalar K) C N} →
  (u : Fourier.AdmissibleFourierShellData
    (orderedScalar K) C N interaction) →
  Contrast.NegativeTransferContrastData
    {A = Support.PhysicalCutoffIncidence N R sector}
    (physicalCutoffFiniteShellInnerProductSpace K N R sector)
canonicalPhysicalCutoffNegativeTransferContrastData
  K C N R sector u =
  Contrast.physicalIndexedCutoffNegativeTransferContrastFromFourierData
    (orderedScalar K) C N R sector
    (physicalCutoffFiniteShellInnerProductSpace K N R sector)
    u
    (physicalIncidenceVector (orderedScalar K) N R sector)

physicalCutoffNegativeTransferContrastGramIdentity :
  (K : ExactOrderedCommutativeRing) →
  (C : Fourier.ComplexFourierInterface (orderedScalar K)) →
  (N R : Nat) → (sector : Sector.ExactOutputRetainedSectorLaw N R) →
  {interaction :
    Fourier.PhysicalTriadInteractionLaw (orderedScalar K) C N} →
  (u : Fourier.AdmissibleFourierShellData
    (orderedScalar K) C N interaction) →
  (z : Coordinates.PhysicalCutoffVector (orderedScalar K) N R sector) →
  Contrast.negativeTransferContrast
    (canonicalPhysicalCutoffNegativeTransferContrastData
      K C N R sector u) z ≡
  Gram.inner (physicalCutoffFiniteShellInnerProductSpace K N R sector) z
    (Contrast.physicalLNeg
      (canonicalPhysicalCutoffNegativeTransferContrastData
        K C N R sector u) z)
physicalCutoffNegativeTransferContrastGramIdentity
  K C N R sector u z =
  Contrast.negativeTransferContrastGramIdentity
    (canonicalPhysicalCutoffNegativeTransferContrastData
      K C N R sector u) z
