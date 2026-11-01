module DASHI.Core.GenderedNormApprovalSourceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenderedNormApprovalIndependenceExact as Formal

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION / CLAIM FIREWALL
--
-- Source: user-supplied SRT transcript, 2026-09-25.
--
-- The transcript presents a rhetorical model in which patriarchal power is
-- compared to software/code, relatability is described as rewarded, refusal
-- to optimise for likability is presented as a loophole, and respect is
-- preferred to likability.  It also invokes Machiavelli rhetorically.
--
-- This module records what the source says.  It does not upgrade those source
-- assertions into empirical facts.  The repository theorem owner proves only
-- the generic finite independence/non-factorability results imported above.
------------------------------------------------------------------------

data SourceClaim : Set where
  patriarchyAsSoftwareMetaphor : SourceClaim
  relatabilityRewardClaim : SourceClaim
  noRefusalPunishmentClaim : SourceClaim
  likabilityVersusRespectClaim : SourceClaim
  likabilityVersusLoyaltyClaim : SourceClaim
  approvalIndependenceStrategyClaim : SourceClaim
  machiavelliRhetoricalAppeal : SourceClaim
  reprogramSystemMetaphor : SourceClaim

data ClaimStatus : Set where
  attributedSourceClaim : ClaimStatus
  externalEvidenceRequired : ClaimStatus

claimStatus : SourceClaim → ClaimStatus
claimStatus patriarchyAsSoftwareMetaphor = attributedSourceClaim
claimStatus relatabilityRewardClaim = externalEvidenceRequired
claimStatus noRefusalPunishmentClaim = externalEvidenceRequired
claimStatus likabilityVersusRespectClaim = externalEvidenceRequired
claimStatus likabilityVersusLoyaltyClaim = externalEvidenceRequired
claimStatus approvalIndependenceStrategyClaim = externalEvidenceRequired
claimStatus machiavelliRhetoricalAppeal = attributedSourceClaim
claimStatus reprogramSystemMetaphor = attributedSourceClaim

sourceKind : String
sourceKind = "user-supplied SRT transcript"

sourceDate : String
sourceDate = "2026-09-25"

sourceClaimLabels : List String
sourceClaimLabels =
  "patriarchy/software metaphor" ∷
  "relatability reward" ∷
  "absence of punishment for refusing approval optimisation" ∷
  "likability distinguished from respect" ∷
  "likability distinguished from loyalty" ∷
  "approval-independent strategy" ∷
  "Machiavelli rhetorical appeal" ∷
  "system reprogramming metaphor" ∷
  []

record SourceFormalisationBoundary : Set where
  constructor sourceFormalisationBoundary
  field
    transcriptIsEmpiricalProof : Bool
    rhetoricalMetaphorIsLiteralMechanism : Bool
    attributedClaimIsRepositoryTheorem : Bool
    genericNonFactorabilityOwnerExists : Bool
    empiricalValidationStillRequired : Bool

open SourceFormalisationBoundary public

canonicalSourceFormalisationBoundary : SourceFormalisationBoundary
canonicalSourceFormalisationBoundary =
  sourceFormalisationBoundary false false false true true

formalBoundary :
  Formal.GenderedNormApprovalBoundary
formalBoundary = Formal.canonicalGenderedNormApprovalBoundary
