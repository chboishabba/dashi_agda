module DASHI.Physics.YangMills.BalabanCMP109Lie3ResolventIdentityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Prove on the literal three-coordinate SU(2) matrix carrier the exact
-- resolvent identity used in the Federbush derivative modulus:
--
--   A_U^{-1} - A_V^{-1}
--     = A_U^{-1} (A_V-A_U) A_V^{-1}.
--
-- The proof first establishes associativity of the repository's finite matrix
-- multiplication by Fubini.  No determinant, spectral theorem, or anonymous
-- operator-algebra axiom is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation

sumScaleRight :
  ∀ {A : Set} (values : List A) (term : A → ℚ) coefficient →
  Sums.sumRational values (λ value → term value * coefficient)
  ≡ Sums.sumRational values term * coefficient
sumScaleRight [] term coefficient = ℚRing.solve []
sumScaleRight (value ∷ values) term coefficient
  rewrite sumScaleRight values term coefficient =
  ℚRing.solve-∀ (term value) (Sums.sumRational values term) coefficient

matrixComposeAssociative : ∀ outer middle inner row column →
  Component.matrixCompose
    (Component.matrixCompose outer middle) inner row column
  ≡ Component.matrixCompose outer
      (Component.matrixCompose middle inner) row column
matrixComposeAssociative outer middle inner row column =
  let
    coordinates = Physical.lieCoordinates3

    expandLeft :
      Component.matrixCompose
        (Component.matrixCompose outer middle) inner row column
      ≡ Sums.sumRational coordinates
          (λ rightMiddle →
            Sums.sumRational coordinates
              (λ leftMiddle →
                (outer row leftMiddle * middle leftMiddle rightMiddle)
                  * inner rightMiddle column))
    expandLeft =
      Sums.sumRationalCong coordinates _ _
        (λ rightMiddle →
          sumScaleRight coordinates
            (λ leftMiddle → outer row leftMiddle * middle leftMiddle rightMiddle)
            (inner rightMiddle column))

    swap :
      Sums.sumRational coordinates
        (λ rightMiddle →
          Sums.sumRational coordinates
            (λ leftMiddle →
              (outer row leftMiddle * middle leftMiddle rightMiddle)
                * inner rightMiddle column))
      ≡ Sums.sumRational coordinates
        (λ leftMiddle →
          Sums.sumRational coordinates
            (λ rightMiddle →
              (outer row leftMiddle * middle leftMiddle rightMiddle)
                * inner rightMiddle column))
    swap = Fubini.sumSwap coordinates coordinates
      (λ rightMiddle leftMiddle →
        (outer row leftMiddle * middle leftMiddle rightMiddle)
          * inner rightMiddle column)

    reassociate :
      Sums.sumRational coordinates
        (λ leftMiddle →
          Sums.sumRational coordinates
            (λ rightMiddle →
              (outer row leftMiddle * middle leftMiddle rightMiddle)
                * inner rightMiddle column))
      ≡ Sums.sumRational coordinates
        (λ leftMiddle →
          outer row leftMiddle
            * Sums.sumRational coordinates
                (λ rightMiddle →
                  middle leftMiddle rightMiddle * inner rightMiddle column))
    reassociate =
      Sums.sumRationalCong coordinates _ _
        (λ leftMiddle →
          trans
            (Sums.sumRationalCong coordinates _ _
              (λ rightMiddle →
                ℚRing.solve-∀
                  (outer row leftMiddle)
                  (middle leftMiddle rightMiddle)
                  (inner rightMiddle column)))
            (Sums.sumRationalScale
              (outer row leftMiddle) coordinates
              (λ rightMiddle →
                middle leftMiddle rightMiddle * inner rightMiddle column)))
  in
  trans expandLeft (trans swap reassociate)

record TwoSidedInversePair
    (matrix inverse : Jacobian.Lie3Matrix) : Set₁ where
  field
    inverseAfterMatrix : ∀ row column →
      Component.matrixCompose inverse matrix row column
      ≡ Jacobian.identity3 row column
    matrixAfterInverse : ∀ row column →
      Component.matrixCompose matrix inverse row column
      ≡ Jacobian.identity3 row column

open TwoSidedInversePair public

leftComposeCong : ∀ outer left right →
  (∀ row column → left row column ≡ right row column) →
  ∀ row column →
  Component.matrixCompose outer left row column
  ≡ Component.matrixCompose outer right row column
leftComposeCong outer left right pointwise row column =
  Sums.sumRationalCong Physical.lieCoordinates3 _ _
    (λ middle → cong (outer row middle *_) (pointwise middle column))

rightComposeCong : ∀ left right inner →
  (∀ row column → left row column ≡ right row column) →
  ∀ row column →
  Component.matrixCompose left inner row column
  ≡ Component.matrixCompose right inner row column
rightComposeCong left right inner pointwise row column =
  Sums.sumRationalCong Physical.lieCoordinates3 _ _
    (λ middle → cong (_* inner middle column) (pointwise row middle))

resolventDifferenceExact :
  ∀ matrixU inverseU matrixV inverseV →
  TwoSidedInversePair matrixU inverseU →
  TwoSidedInversePair matrixV inverseV →
  ∀ row column →
  Variation.matrixDifference inverseU inverseV row column
  ≡ Component.matrixCompose
      (Component.matrixCompose inverseU
        (Variation.matrixDifference matrixV matrixU))
      inverseV row column
resolventDifferenceExact matrixU inverseU matrixV inverseV invU invV row column =
  let
    rhs0 = Component.matrixCompose
      (Component.matrixCompose inverseU
        (Variation.matrixDifference matrixV matrixU))
      inverseV row column

    assoc1 :
      rhs0
      ≡ Component.matrixCompose inverseU
          (Component.matrixCompose
            (Variation.matrixDifference matrixV matrixU) inverseV)
          row column
    assoc1 = matrixComposeAssociative
      inverseU (Variation.matrixDifference matrixV matrixU) inverseV row column

    liftSplit :
      Component.matrixCompose inverseU
        (Component.matrixCompose
          (Variation.matrixDifference matrixV matrixU) inverseV)
        row column
      ≡ Component.matrixCompose inverseU
          (Variation.matrixDifference
            (Component.matrixCompose matrixV inverseV)
            (Component.matrixCompose matrixU inverseV))
          row column
    liftSplit = leftComposeCong inverseU _ _
      (λ r c → Variation.composeDifferenceLeft matrixV matrixU inverseV r c)
      row column

    splitOuter :
      Component.matrixCompose inverseU
        (Variation.matrixDifference
          (Component.matrixCompose matrixV inverseV)
          (Component.matrixCompose matrixU inverseV))
        row column
      ≡ Variation.matrixDifference
          (Component.matrixCompose inverseU
            (Component.matrixCompose matrixV inverseV))
          (Component.matrixCompose inverseU
            (Component.matrixCompose matrixU inverseV))
          row column
    splitOuter = Variation.composeDifferenceRight inverseU
      (Component.matrixCompose matrixV inverseV)
      (Component.matrixCompose matrixU inverseV) row column

    firstToInverseU :
      Component.matrixCompose inverseU
        (Component.matrixCompose matrixV inverseV) row column
      ≡ inverseU row column
    firstToInverseU =
      trans
        (leftComposeCong inverseU
          (Component.matrixCompose matrixV inverseV)
          Jacobian.identity3
          (matrixAfterInverse invV) row column)
        (Component.matrixComposeIdentityRight inverseU row column)

    secondAssoc :
      Component.matrixCompose inverseU
        (Component.matrixCompose matrixU inverseV) row column
      ≡ Component.matrixCompose
          (Component.matrixCompose inverseU matrixU) inverseV row column
    secondAssoc = sym
      (matrixComposeAssociative inverseU matrixU inverseV row column)

    secondToInverseV :
      Component.matrixCompose inverseU
        (Component.matrixCompose matrixU inverseV) row column
      ≡ inverseV row column
    secondToInverseV =
      trans secondAssoc
        (trans
          (rightComposeCong
            (Component.matrixCompose inverseU matrixU)
            Jacobian.identity3 inverseV
            (inverseAfterMatrix invU) row column)
          (Component.matrixComposeIdentityLeft inverseV row column))

    collapse :
      Variation.matrixDifference
        (Component.matrixCompose inverseU
          (Component.matrixCompose matrixV inverseV))
        (Component.matrixCompose inverseU
          (Component.matrixCompose matrixU inverseV))
        row column
      ≡ Variation.matrixDifference inverseU inverseV row column
    collapse =
      trans
        (cong
          (_- Component.matrixCompose inverseU
                (Component.matrixCompose matrixU inverseV) row column)
          firstToInverseU)
        (cong (inverseU row column -_) secondToInverseV)
  in
  sym (trans assoc1 (trans liftSplit (trans splitOuter collapse)))

cmp109Lie3MatrixCompositionAssociativityLevel : ProofLevel
cmp109Lie3MatrixCompositionAssociativityLevel = machineChecked

cmp109Lie3ResolventDifferenceIdentityLevel : ProofLevel
cmp109Lie3ResolventDifferenceIdentityLevel = machineChecked
