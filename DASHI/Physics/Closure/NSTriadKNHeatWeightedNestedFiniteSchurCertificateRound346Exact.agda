module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedFiniteSchurCertificateRound346Exact where

------------------------------------------------------------------------
-- ROUND346 / BIDI: THE FINITE ROW/COLUMN BUDGET LANDS IN THE OLD CERTIFICATE
--
-- R343 already instantiates the old PairIncidenceData on the literal global
-- nested carrier.  `FiniteWeightedKernelSums` and `NSPairIncidenceKernel`
-- already own the exact row/column sum language and the wrapper
-- `PairIncidenceWeightedCertificate`.
--
-- Therefore, assuming the domain lane supplies the two actual finite estimates
-- for the heat-weighted nested coefficient, there is no new Schur theorem to
-- formulate.  This round simply packages those estimates into the old exact
-- finite certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.FiniteWeightedKernelSums as Finite
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact as R343

record NestedFsFiniteSchurInputs
    {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar) : Set₁ where
  field
    rowConstant : Scalar
    columnConstant : Scalar

    rowBound :
      ∀ row →
      Finite._≤_
        (PairKernel.asFiniteWeightedKernel
          (R343.nestedFsPairIncidenceData cutoff S))
        (Finite.rowWeightedSum
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S)) row)
        (Finite.multiply
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S))
          rowConstant
          (PairKernel.rowWeight
            (R343.nestedFsPairIncidenceData cutoff S) row))

    columnBound :
      ∀ col →
      Finite._≤_
        (PairKernel.asFiniteWeightedKernel
          (R343.nestedFsPairIncidenceData cutoff S))
        (Finite.columnWeightedSum
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S)) col)
        (Finite.multiply
          (PairKernel.asFiniteWeightedKernel
            (R343.nestedFsPairIncidenceData cutoff S))
          columnConstant
          (PairKernel.colWeight
            (R343.nestedFsPairIncidenceData cutoff S) col))

open NestedFsFiniteSchurInputs public

nestedFsFiniteSchurCertificate :
  ∀ {Row Col Scalar : Set}
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col Scalar) →
  NestedFsFiniteSchurInputs cutoff S →
  PairKernel.PairIncidenceWeightedCertificate
    (R343.nestedFsPairIncidenceData cutoff S)
nestedFsFiniteSchurCertificate cutoff S B = record
  { finiteCertificate = record
      { rowConstant = rowConstant B
      ; columnConstant = columnConstant B
      ; rowBound = rowBound B
      ; columnBound = columnBound B
      }
  }

round346OldFiniteWeightedKernelSumsReused : Bool
round346OldFiniteWeightedKernelSumsReused = true

round346OldPairIncidenceWeightedCertificateReused : Bool
round346OldPairIncidenceWeightedCertificateReused = true

round346OnlyDomainInputsAreFiniteRowAndColumnBounds : Bool
round346OnlyDomainInputsAreFiniteRowAndColumnBounds = true

round346FiniteSchurPackagingClosed : Bool
round346FiniteSchurPackagingClosed = true

round346AbstractSchurRealizationClosed : Bool
round346AbstractSchurRealizationClosed = false

round346CotlarConsumptionClosed : Bool
round346CotlarConsumptionClosed = false

round346PackageAClosed : Bool
round346PackageAClosed = false

round346ClayPromotion : Bool
round346ClayPromotion = false

round346FiniteSchurPackagingClosedIsTrue :
  round346FiniteSchurPackagingClosed ≡ true
round346FiniteSchurPackagingClosedIsTrue = refl

round346PackageAClosedIsFalse : round346PackageAClosed ≡ false
round346PackageAClosedIsFalse = refl

round346ClayPromotionIsFalse : round346ClayPromotion ≡ false
round346ClayPromotionIsFalse = refl
