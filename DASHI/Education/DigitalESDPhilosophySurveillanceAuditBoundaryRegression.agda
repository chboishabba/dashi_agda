module DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryExact as Audit

visibilityDoesNotCreateAuthority :
  Audit.VisibilityDeterminesParticipantAuthority → ⊥
visibilityDoesNotCreateAuthority = Audit.visibilityDoesNotDetermineParticipantAuthority

philosophyDoesNotCreateEmpiricalEffect :
  Audit.PhilosophyAuditCreatesEmpiricalEffect → ⊥
philosophyDoesNotCreateEmpiricalEffect = Audit.philosophyAuditDoesNotCreateEmpiricalEffect

foucaultDoesNotOwnStudyObservation :
  Audit.FoucaultLensOwnsEmpiricalStudyObservation → ⊥
foucaultDoesNotOwnStudyObservation = Audit.foucaultLensDoesNotOwnEmpiricalStudyObservation
