{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.ColliderChiSquareScopeMatrixExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as CMS
import DASHI.Physics.Closure.W4CalibrationFailureMechanismExact as W4
import DASHI.Promotion.StandardModelHiggsCovariantComparisonLaw as ATLAS

data ColliderComparisonAuthority : Set where
  boundedComparisonLawReceipt : ColliderComparisonAuthority
  fixtureBaselineDiagnostic : ColliderComparisonAuthority
  rejectedProjectionDiagnostic : ColliderComparisonAuthority

record ColliderChiSquareScopeRow : Set where
  constructor colliderChiSquareScopeRow
  field
    experiment : String
    observable : String
    chi2PerDof : String
    degreesOfFreedom : String
    authorityClass : ColliderComparisonAuthority
    empiricalPromotion : Bool
    note : String

open ColliderChiSquareScopeRow public

cmsT43RatioRow : ColliderChiSquareScopeRow
cmsT43RatioRow =
  colliderChiSquareScopeRow
    "CMS"
    "SMP-20-003 t43: phi-star 50--76 / 76--106 GeV mass-window ratio"
    "2.1565191176275618"
    "18"
    boundedComparisonLawReceipt
    true
    "Bounded W3 comparison-law promotion only; does not promote W4/W5/GRQFT."

atlasHiggsFixtureBestRow : ColliderChiSquareScopeRow
atlasHiggsFixtureBestRow =
  colliderChiSquareScopeRow
    "ATLAS"
    "H -> gamma gamma |y_yy| fixture-baseline covariance comparison"
    "2.6493994618998236"
    "6"
    fixtureBaselineDiagnostic
    false
    "Minimum reduced chi-square among four current ATLAS fixture-baseline rows; baseline is explicitly fixture-not-authority, holdout and accepted authority remain absent."

cmsW4AbsoluteRow : ColliderChiSquareScopeRow
cmsW4AbsoluteRow =
  colliderChiSquareScopeRow
    "CMS"
    "SMP-20-003 76--106 GeV absolute d-sigma/d-phi-star current W4 projection"
    "298.8462841768543"
    "17 after one fitted scale"
    rejectedProjectionDiagnostic
    false
    "Current absolute W4 projection is rejected; this does not erase the distinct bounded t43 ratio contact."

canonicalColliderChiSquareScopeRows : List ColliderChiSquareScopeRow
canonicalColliderChiSquareScopeRows =
  cmsT43RatioRow
  ∷ atlasHiggsFixtureBestRow
  ∷ cmsW4AbsoluteRow
  ∷ []

record ColliderChiSquareScopeBoundary : Set where
  constructor colliderChiSquareScopeBoundary
  field
    sameNumericStatisticImpliesSameObservable : Bool
    sameNumericStatisticImpliesSameObservableIsFalse :
      sameNumericStatisticImpliesSameObservable ≡ false

    lowChi2FixtureIsAcceptedEmpiricalAuthority : Bool
    lowChi2FixtureIsAcceptedEmpiricalAuthorityIsFalse :
      lowChi2FixtureIsAcceptedEmpiricalAuthority ≡ false

    rejectedAbsoluteProjectionCancelsBoundedRatioContact : Bool
    rejectedAbsoluteProjectionCancelsBoundedRatioContactIsFalse :
      rejectedAbsoluteProjectionCancelsBoundedRatioContact ≡ false

    rowsMayBeComparedOnlyWithScopeAndAuthorityAttached : Bool
    rowsMayBeComparedOnlyWithScopeAndAuthorityAttachedIsTrue :
      rowsMayBeComparedOnlyWithScopeAndAuthorityAttached ≡ true

open ColliderChiSquareScopeBoundary public

canonicalColliderChiSquareScopeBoundary : ColliderChiSquareScopeBoundary
canonicalColliderChiSquareScopeBoundary =
  colliderChiSquareScopeBoundary
    false refl
    false refl
    false refl
    true refl

cmsBoundedComparisonStillPromoted :
  CMS.W3ComparisonLawAcceptanceCriterion.criterionSatisfied
    CMS.canonicalW3ComparisonLawAcceptanceCriterion
  ≡ true
cmsBoundedComparisonStillPromoted = refl

atlasComparisonSurfaceStillNonPromoting :
  ATLAS.StandardModelHiggsCovariantComparisonLaw.empiricalValidationPromoted
    ATLAS.canonicalStandardModelHiggsCovariantComparisonLaw
  ≡ false
atlasComparisonSurfaceStillNonPromoting =
  ATLAS.canonicalHiggsCovariantComparisonEmpiricalPromotionStillFalse

w4AbsoluteProjectionStillNonPromoting :
  W4.promotesW4 W4.canonicalW4CalibrationFailureDiagnosis ≡ false
w4AbsoluteProjectionStillNonPromoting =
  W4.promotesW4IsFalse W4.canonicalW4CalibrationFailureDiagnosis
