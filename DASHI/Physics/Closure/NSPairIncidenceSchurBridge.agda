module DASHI.Physics.Closure.NSPairIncidenceSchurBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSPairIncidenceKernel

------------------------------------------------------------------------
-- Transport exact finite row/column sums into the existing weighted operator
-- theorem.  The analytic Schur-test realization remains explicit.
------------------------------------------------------------------------

asWeightedKernelData :
  ∀ {p r c s}
    {Pair : Set p} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  PairIncidenceData Pair Row Col Scalar →
  WeightedKernelData Row Col Scalar
asWeightedKernelData P = record
  { kernel = pairKernelEntry P
  ; rowWeight = rowWeight P
  ; colWeight = colWeight P
  }

record PairIncidenceSchurRealization
    {p r c s : Level}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (P : PairIncidenceData Pair Row Col Scalar)
    (L : WeightedSchurLaws (asWeightedKernelData P)) :
    Set (lsuc (p ⊔ r ⊔ c ⊔ s)) where
  field
    finite : PairIncidenceWeightedCertificate P

    rowConstantMatches :
      rowConstant L ≡
      FiniteWeightedSchurCertificate.rowConstant
        (finiteCertificate finite)

    columnConstantMatches :
      columnConstant L ≡
      FiniteWeightedSchurCertificate.columnConstant
        (finiteCertificate finite)

    realizeRowBound :
      (∀ row →
        _≤_ (asFiniteWeightedKernel P)
          (rowWeightedSum (asFiniteWeightedKernel P) row)
          (multiply (asFiniteWeightedKernel P)
            (FiniteWeightedSchurCertificate.rowConstant
              (finiteCertificate finite))
            (rowWeight P row))) →
      rowWeightedBound L

    realizeColumnBound :
      (∀ col →
        _≤_ (asFiniteWeightedKernel P)
          (columnWeightedSum (asFiniteWeightedKernel P) col)
          (multiply (asFiniteWeightedKernel P)
            (FiniteWeightedSchurCertificate.columnConstant
              (finiteCertificate finite))
            (colWeight P col))) →
      columnWeightedBound L

open import Relation.Binary.PropositionalEquality using (_≡_)
open PairIncidenceSchurRealization public

pairIncidenceWeightedCertificate :
  ∀ {p r c s}
    {Pair : Set p} {Row : Set r} {Col : Set c} {Scalar : Set s}
    {P : PairIncidenceData Pair Row Col Scalar}
    {L : WeightedSchurLaws (asWeightedKernelData P)} →
  PairIncidenceSchurRealization P L →
  WeightedKernelSchurCertificate (asWeightedKernelData P) L
pairIncidenceWeightedCertificate R = record
  { rowBound = realizeRowBound R
      (FiniteWeightedSchurCertificate.rowBound
        (finiteCertificate (finite R)))
  ; columnBound = realizeColumnBound R
      (FiniteWeightedSchurCertificate.columnBound
        (finiteCertificate (finite R)))
  }
