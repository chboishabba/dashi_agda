module DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumSwap)

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

    -- The concrete coordinate enumerator establishes the Kronecker action.
    deltaActsAsIdentity : ∀ (vector : Index → ℚ) (row : Index) →
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
sumRationalRightScale [] term coefficient =
  sym (ℚP.*-zeroˡ coefficient)
sumRationalRightScale (value ∷ values) term coefficient
  rewrite sumRationalRightScale values term coefficient =
  sym (ℚP.*-distribʳ-+ coefficient (term value) (sumRational values term))

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
        sym
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
              (λ column → ℚP.*-assoc (left row middle) (right middle column) (vector column)))
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
    (sym
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
    (sym
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
-- Constructive pointwise Green certificate.
--
-- Propositional equality of arbitrary function-valued vectors would require an
-- extensionality principle.  The actual analytic content is pointwise equality,
-- so this interface records exactly that and does not assume function
-- extensionality.  Downstream finite carriers can use a record representation if
-- propositional vector equality is required.
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

record ConstructiveFiniteGreenCertificate (Index : Set) : Set₁ where
  field
    operator inverse : RationalVector Index → RationalVector Index
    inverseLeftPointwise : ∀ vector coordinate →
      inverse (operator vector) coordinate ≡ vector coordinate
    inverseRightPointwise : ∀ vector coordinate →
      operator (inverse vector) coordinate ≡ vector coordinate
    norm : RationalVector Index → ℚ
    reciprocalBound : ℚ
    inverseBound : ∀ vector →
      norm (inverse vector) ≤ reciprocalBound * norm vector

open ConstructiveFiniteGreenCertificate public

constructiveFiniteGreen :
  ∀ {Index} (dataSet : ConstructiveMatrixGreenData Index) →
  ConstructiveFiniteGreenCertificate Index
constructiveFiniteGreen dataSet = record
  { operator = applyMatrix (carrier dataSet) (operatorMatrix dataSet)
  ; inverse = applyMatrix
      (carrier dataSet)
      (inverseMatrix (inverseCertificate dataSet))
  ; inverseLeftPointwise =
      matrixInverseLeftExact (inverseCertificate dataSet)
  ; inverseRightPointwise =
      matrixInverseRightExact (inverseCertificate dataSet)
  ; norm = vectorNorm dataSet
  ; reciprocalBound = reciprocalCoercivity dataSet
  ; inverseBound = inverseNormBound dataSet
  }

finiteMatrixProductActionLevel : ProofLevel
finiteMatrixProductActionLevel = machineChecked

finiteMatrixInverseConsequenceLevel : ProofLevel
finiteMatrixInverseConsequenceLevel = machineChecked

constructivePointwiseGreenAssemblyLevel : ProofLevel
constructivePointwiseGreenAssemblyLevel = machineChecked

configuredMatrixRepresentationProducerLevel : ProofLevel
configuredMatrixRepresentationProducerLevel = conditional

configuredGeneratedInverseProductProducerLevel : ProofLevel
configuredGeneratedInverseProductProducerLevel = conditional
