module DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumSwap)
import DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen as Green

------------------------------------------------------------------------
-- Generic finite rational coordinates and matrices.
------------------------------------------------------------------------

RationalVector : Set → Set
RationalVector Index = Index → ℚ

RationalMatrix : Set → Set
RationalMatrix Index = Index → Index → ℚ

record FiniteRationalCoordinates (Index : Set) : Set₁ where
  field
    coordinates : List Index
    delta : Index → Index → ℚ

    -- The concrete coordinate enumerator must establish the Kronecker action.
    -- This avoids assuming decidable equality or function extensionality here.
    deltaActsAsIdentity : ∀ vector row →
      sumRational coordinates (λ column → delta row column * vector column)
      ≡ vector row

open FiniteRationalCoordinates public

applyMatrix :
  ∀ {Index} → FiniteRationalCoordinates Index →
  RationalMatrix Index → RationalVector Index → RationalVector Index
applyMatrix carrier matrix vector row =
  sumRational (coordinates carrier)
    (λ column → matrix row column * vector column)

multiplyMatrix :
  ∀ {Index} → FiniteRationalCoordinates Index →
  RationalMatrix Index → RationalMatrix Index → RationalMatrix Index
multiplyMatrix carrier left right row column =
  sumRational (coordinates carrier)
    (λ middle → left row middle * right middle column)

sumRationalRightScale :
  ∀ {A : Set} (values : List A) (term : A → ℚ) coefficient →
  sumRational values (λ value → term value * coefficient)
  ≡ sumRational values term * coefficient
sumRationalRightScale [] term coefficient = ℚRing.solve-∀ coefficient
sumRationalRightScale (value ∷ values) term coefficient
  rewrite sumRationalRightScale values term coefficient =
  ℚRing.solve-∀
    (term value) (sumRational values term) coefficient

matrixProductActionExact :
  ∀ {Index}
    (carrier : FiniteRationalCoordinates Index)
    left right vector row →
  applyMatrix carrier (multiplyMatrix carrier left right) vector row
  ≡ applyMatrix carrier left (applyMatrix carrier right vector) row
matrixProductActionExact carrier left right vector row =
  trans
    (sumRationalCong
      (coordinates carrier)
      (λ column →
        sumRational (coordinates carrier)
          (λ middle → left row middle * right middle column)
        * vector column)
      (λ column →
        sumRational (coordinates carrier)
          (λ middle →
            (left row middle * right middle column) * vector column))
      (λ column →
        Relation.Binary.PropositionalEquality.sym
          (sumRationalRightScale
            (coordinates carrier)
            (λ middle → left row middle * right middle column)
            (vector column))))
    (trans
      (sumSwap
        (coordinates carrier)
        (coordinates carrier)
        (λ column middle →
          (left row middle * right middle column) * vector column))
      (sumRationalCong
        (coordinates carrier)
        (λ middle →
          sumRational (coordinates carrier)
            (λ column →
              (left row middle * right middle column) * vector column))
        (λ middle →
          left row middle *
            sumRational (coordinates carrier)
              (λ column → right middle column * vector column))
        (λ middle →
          trans
            (sumRationalCong
              (coordinates carrier)
              (λ column →
                (left row middle * right middle column) * vector column)
              (λ column →
                left row middle * (right middle column * vector column))
              (λ column → ℚRing.solve-∀
                (left row middle) (right middle column) (vector column)))
            (sumRationalScale
              (left row middle)
              (coordinates carrier)
              (λ column → right middle column * vector column)))))

matrixPointwiseActionCong :
  ∀ {Index}
    (carrier : FiniteRationalCoordinates Index)
    (left right : RationalMatrix Index) →
  (∀ row column → left row column ≡ right row column) →
  ∀ vector row →
  applyMatrix carrier left vector row ≡ applyMatrix carrier right vector row
matrixPointwiseActionCong carrier left right pointwise vector row =
  sumRationalCong
    (coordinates carrier)
    (λ column → left row column * vector column)
    (λ column → right row column * vector column)
    (λ column → cong (λ coefficient → coefficient * vector column)
      (pointwise row column))

------------------------------------------------------------------------
-- Exact inverse certificate checked by finite matrix multiplication.
------------------------------------------------------------------------

record RationalMatrixInverseCertificate
    {Index : Set}
    (carrier : FiniteRationalCoordinates Index)
    (operatorMatrix : RationalMatrix Index) : Set₁ where
  field
    inverseMatrix : RationalMatrix Index

    inverseTimesOperator : ∀ row column →
      multiplyMatrix carrier inverseMatrix operatorMatrix row column
      ≡ delta carrier row column

    operatorTimesInverse : ∀ row column →
      multiplyMatrix carrier operatorMatrix inverseMatrix row column
      ≡ delta carrier row column

open RationalMatrixInverseCertificate public

matrixInverseLeftExact :
  ∀ {Index}
    {carrier : FiniteRationalCoordinates Index}
    {operatorMatrix : RationalMatrix Index}
    (certificate : RationalMatrixInverseCertificate carrier operatorMatrix)
    vector row →
  applyMatrix carrier (inverseMatrix certificate)
    (applyMatrix carrier operatorMatrix vector) row
  ≡ vector row
matrixInverseLeftExact {carrier = carrier} {operatorMatrix = operatorMatrix}
    certificate vector row =
  trans
    (Relation.Binary.PropositionalEquality.sym
      (matrixProductActionExact carrier
        (inverseMatrix certificate) operatorMatrix vector row))
    (trans
      (matrixPointwiseActionCong carrier
        (multiplyMatrix carrier (inverseMatrix certificate) operatorMatrix)
        (delta carrier)
        (inverseTimesOperator certificate)
        vector row)
      (deltaActsAsIdentity carrier vector row))

matrixInverseRightExact :
  ∀ {Index}
    {carrier : FiniteRationalCoordinates Index}
    {operatorMatrix : RationalMatrix Index}
    (certificate : RationalMatrixInverseCertificate carrier operatorMatrix)
    vector row →
  applyMatrix carrier operatorMatrix
    (applyMatrix carrier (inverseMatrix certificate) vector) row
  ≡ vector row
matrixInverseRightExact {carrier = carrier} {operatorMatrix = operatorMatrix}
    certificate vector row =
  trans
    (Relation.Binary.PropositionalEquality.sym
      (matrixProductActionExact carrier
        operatorMatrix (inverseMatrix certificate) vector row))
    (trans
      (matrixPointwiseActionCong carrier
        (multiplyMatrix carrier operatorMatrix (inverseMatrix certificate))
        (delta carrier)
        (operatorTimesInverse certificate)
        vector row)
      (deltaActsAsIdentity carrier vector row))

------------------------------------------------------------------------
-- Adapter to the repository Green interface.  Once the literal configured
-- operator is identified with a finite rational matrix and its generated inverse
-- products are checked, no external coercive-inverse theorem is needed.
------------------------------------------------------------------------

record ConstructiveMatrixGreenData (Index : Set) : Set₁ where
  field
    carrier : FiniteRationalCoordinates Index
    operatorMatrix : RationalMatrix Index
    inverseCertificate : RationalMatrixInverseCertificate carrier operatorMatrix

    inner : RationalVector Index → RationalVector Index → ℚ
    vectorNorm energy : RationalVector Index → ℚ
    coercivityConstant reciprocalCoercivity : ℚ

    Positive : ℚ → Set
    positiveCoercivity : Positive coercivityConstant
    Coercive : Set
    coercive : Coercive

    energyDefinition : ∀ vector →
      energy vector ≡ inner vector (applyMatrix carrier operatorMatrix vector)

    inverseNormBound : ∀ vector →
      vectorNorm (applyMatrix carrier
        (inverseMatrix inverseCertificate) vector)
      ≤ reciprocalCoercivity * vectorNorm vector

open ConstructiveMatrixGreenData public

matrixOperatorData :
  ∀ {Index} → ConstructiveMatrixGreenData Index →
  Green.CoerciveFiniteOperator (RationalVector Index) ℚ ℚ
matrixOperatorData dataSet = record
  { Green.operator = applyMatrix (carrier dataSet) (operatorMatrix dataSet)
  ; Green.inner = inner dataSet
  ; Green.vectorNorm = vectorNorm dataSet
  ; Green.energy = energy dataSet
  ; Green.coercivityConstant = coercivityConstant dataSet
  ; Green.LessEqual = _≤_
  ; Green.Positive = Positive dataSet
  ; Green.positiveCoercivity = positiveCoercivity dataSet
  ; Green.energyDefinition = energyDefinition dataSet
  ; Green.Coercive = Coercive dataSet
  ; Green.coercive = coercive dataSet
  }

constructiveFiniteCoerciveInverse :
  ∀ {Index} (dataSet : ConstructiveMatrixGreenData Index) →
  Green.FiniteCoerciveInverseAuthority (matrixOperatorData dataSet)
constructiveFiniteCoerciveInverse dataSet = record
  { Green.inverse = applyMatrix
      (carrier dataSet)
      (inverseMatrix (inverseCertificate dataSet))
  ; Green.inverseLeft = λ vector →
      funPointwise
        (matrixInverseLeftExact (inverseCertificate dataSet) vector)
  ; Green.inverseRight = λ vector →
      funPointwise
        (matrixInverseRightExact (inverseCertificate dataSet) vector)
  ; Green.reciprocalCoercivity = reciprocalCoercivity dataSet
  ; Green.multiplyBound = _*_
  ; Green.inverseNormBound = inverseNormBound dataSet
  }
  where
    -- Function extensionality is deliberately not assumed by the matrix algebra.
    -- The concrete finite coordinate carrier must provide the equality adapter.
    postulate
      funPointwise : ∀ {left right : RationalVector Index} →
        (∀ coordinate → left coordinate ≡ right coordinate) → left ≡ right

finiteMatrixProductActionLevel : ProofLevel
finiteMatrixProductActionLevel = machineChecked

finiteMatrixInverseConsequenceLevel : ProofLevel
finiteMatrixInverseConsequenceLevel = machineChecked

configuredMatrixRepresentationProducerLevel : ProofLevel
configuredMatrixRepresentationProducerLevel = conditional

configuredGeneratedInverseProductProducerLevel : ProofLevel
configuredGeneratedInverseProductProducerLevel = conditional
