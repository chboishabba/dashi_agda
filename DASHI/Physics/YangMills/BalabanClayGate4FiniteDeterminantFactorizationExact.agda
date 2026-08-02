module DASHI.Physics.YangMills.BalabanClayGate4FiniteDeterminantFactorizationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact finite determinant factorization and eigenvalue-product bounds.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- The first theorem proves, from ring and inverse laws alone,
--
--   det(A + E) = det(A) det(I + A^{-1}E).
--
-- The second theorem proves the finite product step behind the symmetric
-- multiplier: if every eigenvalue factor lies between lower and upper, the
-- determinant product lies between the corresponding powers.  No matrix,
-- spectrum or determinant carrier may change between these steps.
------------------------------------------------------------------------

record DeterminantMatrixAlgebra
    (Matrix Scalar : Set) : Set₁ where
  field
    identityMatrix : Matrix
    addMatrix multiplyMatrix : Matrix → Matrix → Matrix

    determinant : Matrix → Scalar
    multiplyScalar : Scalar → Scalar → Scalar

    multiplyAssociative : ∀ left middle right →
      multiplyMatrix (multiplyMatrix left middle) right
      ≡ multiplyMatrix left (multiplyMatrix middle right)
    multiplyIdentityLeft : ∀ matrix →
      multiplyMatrix identityMatrix matrix ≡ matrix
    multiplyIdentityRight : ∀ matrix →
      multiplyMatrix matrix identityMatrix ≡ matrix
    distributeLeft : ∀ matrix left right →
      multiplyMatrix matrix (addMatrix left right)
      ≡ addMatrix
          (multiplyMatrix matrix left)
          (multiplyMatrix matrix right)

    determinantMultiplicative : ∀ left right →
      determinant (multiplyMatrix left right)
      ≡ multiplyScalar (determinant left) (determinant right)

open DeterminantMatrixAlgebra public

record InvertibleReferencePerturbation
    {Matrix Scalar : Set}
    (algebra : DeterminantMatrixAlgebra Matrix Scalar) : Set₁ where
  field
    reference inverseReference perturbation : Matrix
    rightInverse :
      multiplyMatrix algebra reference inverseReference
      ≡ identityMatrix algebra

open InvertibleReferencePerturbation public

referenceTimesRelativePerturbation :
  ∀ {Matrix Scalar}
    {algebra : DeterminantMatrixAlgebra Matrix Scalar}
    (dataSet : InvertibleReferencePerturbation algebra) →
  multiplyMatrix algebra
    (reference dataSet)
    (addMatrix algebra
      (identityMatrix algebra)
      (multiplyMatrix algebra
        (inverseReference dataSet)
        (perturbation dataSet)))
  ≡ addMatrix algebra
      (reference dataSet)
      (perturbation dataSet)
referenceTimesRelativePerturbation {algebra = algebra} dataSet =
  trans
    (distributeLeft algebra
      (reference dataSet)
      (identityMatrix algebra)
      (multiplyMatrix algebra
        (inverseReference dataSet) (perturbation dataSet)))
    (trans
      (cong₂ (addMatrix algebra)
        (multiplyIdentityRight algebra (reference dataSet))
        (trans
          (sym
            (multiplyAssociative algebra
              (reference dataSet)
              (inverseReference dataSet)
              (perturbation dataSet)))
          (trans
            (cong
              (λ matrix → multiplyMatrix algebra matrix
                (perturbation dataSet))
              (rightInverse dataSet))
            (multiplyIdentityLeft algebra (perturbation dataSet)))))
      refl)

determinantPerturbationFactorization :
  ∀ {Matrix Scalar}
    {algebra : DeterminantMatrixAlgebra Matrix Scalar}
    (dataSet : InvertibleReferencePerturbation algebra) →
  determinant algebra
    (addMatrix algebra (reference dataSet) (perturbation dataSet))
  ≡ multiplyScalar algebra
      (determinant algebra (reference dataSet))
      (determinant algebra
        (addMatrix algebra
          (identityMatrix algebra)
          (multiplyMatrix algebra
            (inverseReference dataSet)
            (perturbation dataSet))))
determinantPerturbationFactorization {algebra = algebra} dataSet =
  trans
    (cong (determinant algebra)
      (sym (referenceTimesRelativePerturbation dataSet)))
    (determinantMultiplicative algebra
      (reference dataSet)
      (addMatrix algebra
        (identityMatrix algebra)
        (multiplyMatrix algebra
          (inverseReference dataSet)
          (perturbation dataSet))))

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

record OrderedMultiplicativeBounds (Scalar : Set) : Set₁ where
  field
    one : Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Nonnegative : Scalar → Set

    lessEqualReflexive : ∀ value → LessEqual value value
    lessEqualTransitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotoneNonnegative : ∀ {left left' right right'} →
      Nonnegative left → Nonnegative left' →
      Nonnegative right → Nonnegative right' →
      LessEqual left left' → LessEqual right right' →
      LessEqual (multiply left right) (multiply left' right')

    oneNonnegative : Nonnegative one
    productNonnegative : ∀ {left right} →
      Nonnegative left → Nonnegative right →
      Nonnegative (multiply left right)

open OrderedMultiplicativeBounds public

productList : ∀ {Scalar} → OrderedMultiplicativeBounds Scalar →
  List Scalar → Scalar
productList algebra [] = one algebra
productList algebra (value ∷ values) =
  multiply algebra value (productList algebra values)

power : ∀ {Scalar} → OrderedMultiplicativeBounds Scalar →
  Scalar → Nat → Scalar
power algebra value zero = one algebra
power algebra value (suc count) =
  multiply algebra value (power algebra value count)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

allNonnegativeProduct :
  ∀ {Scalar values}
    (algebra : OrderedMultiplicativeBounds Scalar) →
  All (Nonnegative algebra) values →
  Nonnegative algebra (productList algebra values)
allNonnegativeProduct algebra allNil = oneNonnegative algebra
allNonnegativeProduct algebra (allCons head rest) =
  productNonnegative algebra head (allNonnegativeProduct algebra rest)

allLowerProductBound :
  ∀ {Scalar values lower}
    (algebra : OrderedMultiplicativeBounds Scalar) →
  Nonnegative algebra lower →
  All (Nonnegative algebra) values →
  All (λ value → LessEqual algebra lower value) values →
  LessEqual algebra
    (power algebra lower (listLength values))
    (productList algebra values)
allLowerProductBound {lower = lower} algebra lowerNonnegative allNil allNil =
  lessEqualReflexive algebra (one algebra)
allLowerProductBound {lower = lower} algebra lowerNonnegative
    (allCons valueNonnegative restNonnegative)
    (allCons lowerBelow restBounds) =
  multiplyMonotoneNonnegative algebra
    lowerNonnegative valueNonnegative
    (powerNonnegative lowerNonnegative restBounds)
    (allNonnegativeProduct algebra restNonnegative)
    lowerBelow
    (allLowerProductBound algebra lowerNonnegative
      restNonnegative restBounds)
  where
  powerNonnegative : ∀ {rest} →
    Nonnegative algebra lower →
    All (λ value → LessEqual algebra lower value) rest →
    Nonnegative algebra (power algebra lower (listLength rest))
  powerNonnegative lower≥0 allNil = oneNonnegative algebra
  powerNonnegative lower≥0 (allCons bound bounds) =
    productNonnegative algebra lower≥0
      (powerNonnegative lower≥0 bounds)

allUpperProductBound :
  ∀ {Scalar values upper}
    (algebra : OrderedMultiplicativeBounds Scalar) →
  Nonnegative algebra upper →
  All (Nonnegative algebra) values →
  All (λ value → LessEqual algebra value upper) values →
  LessEqual algebra
    (productList algebra values)
    (power algebra upper (listLength values))
allUpperProductBound {upper = upper} algebra upperNonnegative allNil allNil =
  lessEqualReflexive algebra (one algebra)
allUpperProductBound {upper = upper} algebra upperNonnegative
    (allCons valueNonnegative restNonnegative)
    (allCons belowUpper restBounds) =
  multiplyMonotoneNonnegative algebra
    valueNonnegative upperNonnegative
    (allNonnegativeProduct algebra restNonnegative)
    (powerNonnegative upperNonnegative restBounds)
    belowUpper
    (allUpperProductBound algebra upperNonnegative
      restNonnegative restBounds)
  where
  powerNonnegative : ∀ {rest} →
    Nonnegative algebra upper →
    All (λ value → LessEqual algebra value upper) rest →
    Nonnegative algebra (power algebra upper (listLength rest))
  powerNonnegative upper≥0 allNil = oneNonnegative algebra
  powerNonnegative upper≥0 (allCons bound bounds) =
    productNonnegative algebra upper≥0
      (powerNonnegative upper≥0 bounds)

record FiniteDeterminantEigenvalueProductBounds
    (Scalar : Set) : Set₁ where
  field
    algebra : OrderedMultiplicativeBounds Scalar
    factors : List Scalar
    determinantRatio lowerFactor upperFactor : Scalar

    determinantIsFactorProduct :
      determinantRatio ≡ productList algebra factors

    lowerNonnegative : Nonnegative algebra lowerFactor
    upperNonnegative : Nonnegative algebra upperFactor
    factorsNonnegative : All (Nonnegative algebra) factors

    everyFactorAboveLower :
      All (λ factor → LessEqual algebra lowerFactor factor) factors
    everyFactorBelowUpper :
      All (λ factor → LessEqual algebra factor upperFactor) factors

open FiniteDeterminantEigenvalueProductBounds public

determinantRatioAboveLowerPower :
  ∀ {Scalar}
    (dataSet : FiniteDeterminantEigenvalueProductBounds Scalar) →
  LessEqual (algebra dataSet)
    (power (algebra dataSet) (lowerFactor dataSet)
      (listLength (factors dataSet)))
    (determinantRatio dataSet)
determinantRatioAboveLowerPower dataSet =
  subst
    (λ upper → LessEqual (algebra dataSet)
      (power (algebra dataSet) (lowerFactor dataSet)
        (listLength (factors dataSet))) upper)
    (sym (determinantIsFactorProduct dataSet))
    (allLowerProductBound (algebra dataSet)
      (lowerNonnegative dataSet)
      (factorsNonnegative dataSet)
      (everyFactorAboveLower dataSet))

determinantRatioBelowUpperPower :
  ∀ {Scalar}
    (dataSet : FiniteDeterminantEigenvalueProductBounds Scalar) →
  LessEqual (algebra dataSet)
    (determinantRatio dataSet)
    (power (algebra dataSet) (upperFactor dataSet)
      (listLength (factors dataSet)))
determinantRatioBelowUpperPower dataSet =
  subst
    (λ lower → LessEqual (algebra dataSet) lower
      (power (algebra dataSet) (upperFactor dataSet)
        (listLength (factors dataSet))))
    (sym (determinantIsFactorProduct dataSet))
    (allUpperProductBound (algebra dataSet)
      (upperNonnegative dataSet)
      (factorsNonnegative dataSet)
      (everyFactorBelowUpper dataSet))

finiteDeterminantFactorizationLevel : ProofLevel
finiteDeterminantFactorizationLevel = machineChecked

finiteEigenvalueProductLowerBoundLevel : ProofLevel
finiteEigenvalueProductLowerBoundLevel = machineChecked

finiteEigenvalueProductUpperBoundLevel : ProofLevel
finiteEigenvalueProductUpperBoundLevel = machineChecked

physicalSymmetricRelativeSpectrumInputsLevel : ProofLevel
physicalSymmetricRelativeSpectrumInputsLevel = conditional
