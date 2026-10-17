module DASHI.Governance.BoloBoloOWSContemporaneousSpokesWitnessRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloOWSContemporaneousSpokesWitnessExact as Witness

libraryRecordsAreContemporaneous :
  Witness.contemporaneousMovementEvidencePaid
    Witness.canonicalContemporaneousSpokesBoundary ≡ true
libraryRecordsAreContemporaneous = refl

notPrimarySpokesMinutes :
  Witness.underlyingSpokesPrimaryMinutesPaid
    Witness.canonicalContemporaneousSpokesBoundary ≡ false
notPrimarySpokesMinutes = refl

rotationRecallSurfacePaid :
  Witness.rotationRecallProposalSurfacePaid
    Witness.canonicalContemporaneousSpokesBoundary ≡ true
rotationRecallSurfacePaid = refl

reportbackSurfacePaid :
  Witness.workingGroupReportbackSurfacePaid
    Witness.canonicalContemporaneousSpokesBoundary ≡ true
reportbackSurfacePaid = refl

noCausalEffect :
  Witness.contemporaneousRecordsIdentifySpokesCausalEffect
    Witness.canonicalContemporaneousSpokesBoundary ≡ false
noCausalEffect = refl
