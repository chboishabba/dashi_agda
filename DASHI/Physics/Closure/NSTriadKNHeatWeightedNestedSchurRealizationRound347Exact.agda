module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSchurRealizationRound347Exact where

------------------------------------------------------------------------
-- ROUND347 / BIDI: TRANSPORT THE FINITE CERTIFICATE THROUGH THE OLD SCHUR BRIDGE
--
-- R346 produces exactly `PairIncidenceWeightedCertificate`.  The repository
-- already owns `PairIncidenceSchurRealization`, whose only job is to identify
-- the finite constants with the abstract WeightedSchurLaws constants and
-- transport the exact finite row/column inequalities into that law package.
--
-- Consequently the new nested F_s lane needs no bespoke weighted-Schur layer.
-- Given the already-required realization receipts, it inhabits the old bridge
-- directly and inherits `WeightedKernelSchurCertificate` downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.FiniteWeightedKernelSums as Finite
import DASHI.Analysis.WeightedKernelSchurTest as Weighted
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSPairIncidenceSchurBridge as PairSchur
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact as R343
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedFiniteSchurCertificateRound346Exact as R346

nestedFsSchurRealization :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar)
    (B : R346.NestedFsFiniteSchurInputs cutoff S)
    (L : Weighted.WeightedSchurLaws
      (PairSchur.asWeightedKernelData
        (R343.nestedFsPairIncidenceData cutoff S)))
    (rowConstantMatches :
      Weighted.rowConstant L ≡
      Finite.rowConstant
        (PairKernel.finiteCertificate
          (R346.nestedFsFiniteSchurCertificate cutoff S B)))
    (columnConstantMatches :
      Weighted.columnConstant L ≡
      Finite.columnConstant
        (PairKernel.finiteCertificate
          (R346.nestedFsFiniteSchurCertificate cutoff S B)))
    (realizeRowBound :
      (∀ row →
        Finite._≤_
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S))
          (Finite.rowWeightedSum
            (PairKernel.asFiniteWeightedKernel
              (R343.nestedFsPairIncidenceData cutoff S)) row)
          (Finite.multiply
            (PairKernel.asFiniteWeightedKernel
              (R343.nestedFsPairIncidenceData cutoff S))
            (Finite.rowConstant
              (PairKernel.finiteCertificate
                (R346.nestedFsFiniteSchurCertificate cutoff S B)))
            (PairKernel.rowWeight
              (R343.nestedFsPairIncidenceData cutoff S) row))) →
      Weighted.rowWeightedBound L)
    (realizeColumnBound :
      (∀ col →
        Finite._≤_
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S))
          (Finite.columnWeightedSum
            (PairKernel.asFiniteWeightedKernel
              (R343.nestedFsPairIncidenceData cutoff S)) col)
          (Finite.multiply
            (PairKernel.asFiniteWeightedKernel
              (R343.nestedFsPairIncidenceData cutoff S))
            (Finite.columnConstant
              (PairKernel.finiteCertificate
                (R346.nestedFsFiniteSchurCertificate cutoff S B)))
            (PairKernel.colWeight
              (R343.nestedFsPairIncidenceData cutoff S) col))) →
      Weighted.columnWeightedBound L) →
  PairSchur.PairIncidenceSchurRealization
    (R343.nestedFsPairIncidenceData cutoff S) L
nestedFsSchurRealization
  cutoff S B L rowMatch columnMatch realizeRow realizeColumn = record
  { finite = R346.nestedFsFiniteSchurCertificate cutoff S B
  ; rowConstantMatches = rowMatch
  ; columnConstantMatches = columnMatch
  ; realizeRowBound = realizeRow
  ; realizeColumnBound = realizeColumn
  }

nestedFsWeightedKernelSchurCertificate :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar)
    (B : R346.NestedFsFiniteSchurInputs cutoff S)
    (L : Weighted.WeightedSchurLaws
      (PairSchur.asWeightedKernelData
        (R343.nestedFsPairIncidenceData cutoff S))) →
  PairSchur.PairIncidenceSchurRealization
    (R343.nestedFsPairIncidenceData cutoff S) L →
  Weighted.WeightedKernelSchurCertificate
    (PairSchur.asWeightedKernelData
      (R343.nestedFsPairIncidenceData cutoff S)) L
nestedFsWeightedKernelSchurCertificate cutoff S B L R =
  PairSchur.pairIncidenceWeightedCertificate R

round347OldPairIncidenceSchurRealizationReused : Bool
round347OldPairIncidenceSchurRealizationReused = true

round347NoNestedSpecificWeightedSchurOntology : Bool
round347NoNestedSpecificWeightedSchurOntology = true

round347FiniteCertificateComesDirectlyFromR346 : Bool
round347FiniteCertificateComesDirectlyFromR346 = true

round347WeightedSchurCertificateCompilerClosed : Bool
round347WeightedSchurCertificateCompilerClosed = true

round347PhysicalResponseToWeightedBoundClosed : Bool
round347PhysicalResponseToWeightedBoundClosed = false

round347CotlarConsumptionClosed : Bool
round347CotlarConsumptionClosed = false

round347PackageAClosed : Bool
round347PackageAClosed = false

round347ClayPromotion : Bool
round347ClayPromotion = false

round347WeightedSchurCertificateCompilerClosedIsTrue :
  round347WeightedSchurCertificateCompilerClosed ≡ true
round347WeightedSchurCertificateCompilerClosedIsTrue = refl

round347PackageAClosedIsFalse : round347PackageAClosed ≡ false
round347PackageAClosedIsFalse = refl

round347ClayPromotionIsFalse : round347ClayPromotion ≡ false
round347ClayPromotionIsFalse = refl
