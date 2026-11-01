module DASHI.Core.InstitutionalStatusSignalAdequacyRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.InstitutionalStatusSignalAdequacyExact as Status

substantiveAdequacyDefectRegression :
  Status.SubstantiveAdequacyQueryDefect
substantiveAdequacyDefectRegression = Status.substantiveAdequacyQueryDefect

statusNotAdequacyRegression :
  Status.statusSignalAutomaticallySubstantiveAdequacy
    Status.canonicalInstitutionalStatusSignalBoundary
  ≡ false
statusNotAdequacyRegression = refl

familiarityNotTruthRegression :
  Status.institutionalFamiliarityAutomaticallyTruth
    Status.canonicalInstitutionalStatusSignalBoundary
  ≡ false
familiarityNotTruthRegression = refl

credentialNotCaseFitRegression :
  Status.credentialAutomaticallyConsumerSpecificFit
    Status.canonicalInstitutionalStatusSignalBoundary
  ≡ false
credentialNotCaseFitRegression = refl

statusCanBeRetainedSeparateRegression :
  Status.statusAndSubstantiveCoordinatesRemainSeparate
    Status.canonicalInstitutionalStatusSignalBoundary
  ≡ true
statusCanBeRetainedSeparateRegression = refl
