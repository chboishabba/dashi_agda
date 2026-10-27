module DASHI.Law.SensibLawMaboBrennanRecognitionFormalDemandExact where

------------------------------------------------------------------------
-- Exact source-to-demand witness for the live Mabo Brennan recognition demand.
--
-- This module deliberately proves only a bounded formal-premise relation:
-- the live SLR demand is tied to the already-reviewed Brennan proposition,
-- the existing recognition-basis residual/search, and the existing formal
-- recognition decomposition.
-- Kernel acceptance of this module does not prove judicial truth.
-- Kernel acceptance of this module does not establish legal applicability.
-- Kernel acceptance of this module does not promote claim truth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as Foothold
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

formalPremiseOnly : Bool
formalPremiseOnly = true

createsJudicialAuthority : Bool
createsJudicialAuthority = false

createsLegalAuthority : Bool
createsLegalAuthority = false

promotesApplicability : Bool
promotesApplicability = false

promotesClaimTruth : Bool
promotesClaimTruth = false

formalPremiseOnlyIsTrue : formalPremiseOnly ≡ true
formalPremiseOnlyIsTrue = refl

createsJudicialAuthorityIsFalse : createsJudicialAuthority ≡ false
createsJudicialAuthorityIsFalse = refl

createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
createsLegalAuthorityIsFalse = refl

promotesApplicabilityIsFalse : promotesApplicability ≡ false
promotesApplicabilityIsFalse = refl

promotesClaimTruthIsFalse : promotesClaimTruth ≡ false
promotesClaimTruthIsFalse = refl

------------------------------------------------------------------------
-- Pinned live demand coordinates.
------------------------------------------------------------------------

record MaboBrennanFormalDemandWitness : Set where
  constructor maboBrennanFormalDemandWitness
  field
    demandReference : String
    obligationReference : String
    residualReference : String
    pnfRevisionReference : String
    sourceRevisionReference : String
    statementDigest : String

    reviewedProposition : Mabo.ReviewedJudicialProposition
    reviewedPropositionIsBrennan :
      reviewedProposition ≡ Mabo.brennanSurvivalProposition

    reviewedResidual : Mabo.MaboControversyResidual
    reviewedResidualIsBrennanDawson :
      reviewedResidual ≡ Mabo.brennanDawsonResidual

    recognitionSearch : Mabo.CompiledMaboResidualSearch
    recognitionSearchIsCanonical :
      recognitionSearch ≡ Mabo.brennanDawsonSearch
    searchTargetsRecognitionBasis :
      Mabo.obligation recognitionSearch ≡ Mabo.inspectRecognitionBasis

    recognitionFoothold : Foothold.MaboFoothold
    recognitionFootholdIsCanonical :
      recognitionFoothold ≡ Foothold.canonicalMaboFoothold
    commonLawRecognitionAvailableIsTrue :
      Foothold.commonLawRecognitionAvailable recognitionFoothold ≡ true
    noNewLegislativeRightRequired :
      Foothold.newLegislativeRightRequiredForRecognition recognitionFoothold ≡ false

    reviewedTruthStatusIsUnresolved :
      Mabo.truthStatus reviewedProposition ≡ Status.truthUnresolved

open MaboBrennanFormalDemandWitness public

liveMaboBrennanFormalDemandWitness : MaboBrennanFormalDemandWitness
liveMaboBrennanFormalDemandWitness = maboBrennanFormalDemandWitness
  "formal-demand:mabo:sha256:13390b7c3eff34f6c4f55344f752c2d2cef0297faa0b8d88c7531524d3a98b00"
  "legal-obligation:sha256:0e2069ea33d2b65d1217f6d968ec68c40b70a7cccfb2657465d5e744d88a3203"
  "legal-residual:sha256:b4d23fa12e52365ad69824b861cfbd00338e850e2e83ab3083f85be001042801"
  "pnf-factor-revision:real-matter:mabo:brennan:recognition:v1"
  "external-source-revision:sha256:ba30975a1421963fc13c8e2a40c58d466c49c8236db4676557942a5ed3fad7a0"
  "sha256:a5577814404b3140006d54df57f46e49c24f55cf63701c2569ff38a5c8b9e224"
  Mabo.brennanSurvivalProposition
  refl
  Mabo.brennanDawsonResidual
  refl
  Mabo.brennanDawsonSearch
  refl
  Mabo.searchTargetsRecognitionBasis
  Foothold.canonicalMaboFoothold
  refl
  refl
  Foothold.maboRecognisesRatherThanLegislativelyCreates
  refl

------------------------------------------------------------------------
-- Named projections for the artifact/kernel runner and source regression.
------------------------------------------------------------------------

liveDemandReference : String
liveDemandReference = demandReference liveMaboBrennanFormalDemandWitness

liveObligationReference : String
liveObligationReference = obligationReference liveMaboBrennanFormalDemandWitness

liveResidualReference : String
liveResidualReference = residualReference liveMaboBrennanFormalDemandWitness

livePnfRevisionReference : String
livePnfRevisionReference = pnfRevisionReference liveMaboBrennanFormalDemandWitness

liveSourceRevisionReference : String
liveSourceRevisionReference = sourceRevisionReference liveMaboBrennanFormalDemandWitness

liveStatementDigest : String
liveStatementDigest = statementDigest liveMaboBrennanFormalDemandWitness

liveReviewedTruthStatusIsUnresolved :
  Mabo.truthStatus (reviewedProposition liveMaboBrennanFormalDemandWitness)
    ≡ Status.truthUnresolved
liveReviewedTruthStatusIsUnresolved =
  MaboBrennanFormalDemandWitness.reviewedTruthStatusIsUnresolved
    liveMaboBrennanFormalDemandWitness
