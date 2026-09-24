module DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinExact as Y

yunupinguTreatmentRemainsRequired :
  Y.yunupinguTreatmentIsRequired Y.canonicalYindjibarndiEmpiricalJoinBoundary ≡ true
yunupinguTreatmentRemainsRequired = refl

specificMaboTreatmentRemainsRequired :
  Y.specificMaboTreatmentIsRequired Y.canonicalYindjibarndiEmpiricalJoinBoundary ≡ true
specificMaboTreatmentRemainsRequired = refl

genericMaboAdjacencyRemainsForbidden :
  Y.genericMaboAdjacencyIsRequired Y.canonicalYindjibarndiEmpiricalJoinBoundary ≡ false
genericMaboAdjacencyRemainsForbidden = refl

opposingTreatmentsRemainRepresentable :
  Y.opposingAuthorityTreatmentsCoexist Y.canonicalYindjibarndiEmpiricalJoinBoundary ≡ true
opposingTreatmentsRemainRepresentable = refl

reviewedTreatmentsRemainNonPromoting :
  Y.reviewedTreatmentCreatesClaimTruth Y.canonicalYindjibarndiEmpiricalJoinBoundary ≡ false
reviewedTreatmentsRemainNonPromoting = refl

genericMaboPaymentStillUninhabited :
  Y.GenericMaboDependencyPaid → ⊥
genericMaboPaymentStillUninhabited =
  Y.genericMaboAdjacencyDoesNotPayYindjibarndi
