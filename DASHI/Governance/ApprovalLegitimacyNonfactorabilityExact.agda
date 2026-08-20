module DASHI.Governance.ApprovalLegitimacyNonfactorabilityExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A recorded approval can be identical while the surrounding procedure differs
-- in contestability, consent, scope or current authority.  Therefore approval
-- provenance alone cannot factor a legitimacy judgement.  This is the exact
-- non-factorability theorem behind the LES governance boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic


data ApprovalSurface : Set where
  recordedApproved : ApprovalSurface

data ProceduralState : Set where
  scopedContestableApproval unscopedUnappealableApproval : ProceduralState

data LegitimacyAssessment : Set where
  procedurallyAdmissible procedurallyDefective : LegitimacyAssessment

approvalProjection : ProceduralState → ApprovalSurface
approvalProjection scopedContestableApproval = recordedApproved
approvalProjection unscopedUnappealableApproval = recordedApproved

legitimacy : ProceduralState → LegitimacyAssessment
legitimacy scopedContestableApproval = procedurallyAdmissible
legitimacy unscopedUnappealableApproval = procedurallyDefective

approvalCannotDetermineLegitimacy :
  Core.ConsumerDescentDefect approvalProjection legitimacy
approvalCannotDetermineLegitimacy =
  Core.consumerDescentDefect
    scopedContestableApproval
    unscopedUnappealableApproval
    refl
    impossible
  where
    impossible : procedurallyAdmissible ≡ procedurallyDefective → ⊥
    impossible ()

------------------------------------------------------------------------
-- Reuse the existing diachronic authority theorem rather than inventing a
-- second revocation semantics: historical relevance does not restore current
-- delegated authority.
------------------------------------------------------------------------

historicalEvidenceDoesNotRestoreAuthority :
  Diachronic.historicalEvidenceRestoresAuthority
    Diachronic.canonicalDiachronicAuthorityPromotionBoundary
  ≡ false
historicalEvidenceDoesNotRestoreAuthority =
  Diachronic.canonicalHistoricalEvidenceRestoresAuthorityFalse

record ProceduralLegitimacyBoundary : Set where
  constructor proceduralLegitimacyBoundary
  field
    approvalRecordDoesNotDetermineLegitimacy : Bool
    scopeAndContestabilityAreIndependentCoordinates : Bool
    revocationDoesNotEraseHistory : Bool
    historicalEvidenceDoesNotRestoreCurrentAuthority : Bool

canonicalProceduralLegitimacyBoundary : ProceduralLegitimacyBoundary
canonicalProceduralLegitimacyBoundary =
  proceduralLegitimacyBoundary true true true true
