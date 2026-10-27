{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceTOERegression where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.SensibLawSemanticPromotionPolicy as Semantic
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Legal
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as Follow
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as Native
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact as Provider
import DASHI.Governance.ConsumerSafeGovernancePromotionExact as Governance

------------------------------------------------------------------------
-- SENSIBLAW / LEGAL-FOLLOW / GOVERNANCE -> DASHI TOE
--
-- This file is a regression owner only.
-- It reuses existing theorem owners.
-- It does not create legal truth.
-- It does not create legal authority.
-- It does not create runtime authority.
-- It does not identify Actionstep or another external system with a legal
-- theorem owner.
------------------------------------------------------------------------

legalAuthorityPromoted : Bool
legalAuthorityPromoted =
  Authority.legalAuthorityFlag Semantic.semanticPromotionAuthorityBoundary

legalAuthorityRemainsClosed :
  legalAuthorityPromoted ≡ false
legalAuthorityRemainsClosed =
  Semantic.semantic-promotion-legal-authority-closed

allSemanticAuthorityRemainsClosed :
  Authority.promotesAnyAuthority Semantic.semanticPromotionAuthorityBoundary
  ≡ false
allSemanticAuthorityRemainsClosed =
  Semantic.semantic-promotion-all-authority-closed

expertProductionAuthorityRemainsClosed :
  Expert.expertProductionPromotesAnyAuthority ≡ false
expertProductionAuthorityRemainsClosed =
  Expert.expertProductionPromotesAnyAuthorityIsFalse

candidateLegalSourceDoesNotCreateAuthority :
  Legal.legalSourceRecordAloneIsAuthority
    Legal.canonicalLegalSourceAuthorityBoundary
  ≡ false
candidateLegalSourceDoesNotCreateAuthority =
  Agda.Builtin.Equality.refl

semanticAdmissionCannotSubstituteForLegalAuthority :
  Legal.semanticAdmissionAuthorityCanSubstitute
    Legal.canonicalLegalSourceAuthorityBoundary
  ≡ false
semanticAdmissionCannotSubstituteForLegalAuthority =
  Agda.Builtin.Equality.refl

legalAuthorityAloneDoesNotEstablishApplicability :
  Legal.legalSourceAuthorityAloneEstablishesApplicability
    Legal.canonicalLegalSourceAuthorityBoundary
  ≡ false
legalAuthorityAloneDoesNotEstablishApplicability =
  Agda.Builtin.Equality.refl

legalFollowAcquisitionDoesNotPayResidual :
  Follow.acquisitionEqualsResidualPayment
    Follow.canonicalLegalFollowProofSearchBoundary
  ≡ false
legalFollowAcquisitionDoesNotPayResidual =
  Follow.acquisitionEqualsResidualPaymentIsFalse
    Follow.canonicalLegalFollowProofSearchBoundary

nativeLegalFollowDoesNotCreateLegalAuthority :
  Native.nativeCliCreatesLegalAuthority
    Native.canonicalNativeLegalFollowCliBoundary
  ≡ false
nativeLegalFollowDoesNotCreateLegalAuthority =
  Native.nativeCliCreatesLegalAuthorityIsFalse
    Native.canonicalNativeLegalFollowCliBoundary

providerFailureIsNotNegativeLegalEvidence :
  Provider.providerFailureCountsAsNegativeLegalEvidence
    Provider.canonicalProviderFailureCalibration
  ≡ false
providerFailureIsNotNegativeLegalEvidence =
  Provider.providerFailureCountsAsNegativeLegalEvidenceIsFalse
    Provider.canonicalProviderFailureCalibration

governancePromotionDoesNotCreatePoliticalAuthority :
  Governance.promotionCreatesPoliticalAuthority
    Governance.canonicalConsumerSafeGovernancePromotionBoundary
  ≡ false
governancePromotionDoesNotCreatePoliticalAuthority =
  Agda.Builtin.Equality.refl

heuristicEvidenceCannotPromote :
  ∀ heuristicFor heuristicAgainst target source →
  Semantic.promote
    (Semantic.heuristicCandidate heuristicFor heuristicAgainst target source)
  ≡ DASHI.Algebra.TetralemmaBridge.neither
heuristicEvidenceCannotPromote =
  Semantic.heuristic-only-abstains

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F frame.
--
-- O: central semantic policy surface.
-- R: closed authority-risk boundary.
-- C: bounded legal-follow contract.
-- S: native runtime state boundary.
-- L: legal-source authority lattice boundary.
-- P: consumer-safe promotion policy.
-- G: expert/governance non-promotion boundary.
-- F: exact residual postconditions.
------------------------------------------------------------------------

record SensibLawGovernanceTOEPostconditions : Set where
  field
    semanticLegalAuthorityClosed :
      legalAuthorityPromoted ≡ false

    semanticAllAuthorityClosed :
      Authority.promotesAnyAuthority
        Semantic.semanticPromotionAuthorityBoundary
      ≡ false

    expertAuthorityClosed :
      Expert.expertProductionPromotesAnyAuthority ≡ false

    candidateSourceNotAuthority :
      Legal.legalSourceRecordAloneIsAuthority
        Legal.canonicalLegalSourceAuthorityBoundary
      ≡ false

    semanticAdmissionNotLegalAuthority :
      Legal.semanticAdmissionAuthorityCanSubstitute
        Legal.canonicalLegalSourceAuthorityBoundary
      ≡ false

    legalAuthorityNotApplicability :
      Legal.legalSourceAuthorityAloneEstablishesApplicability
        Legal.canonicalLegalSourceAuthorityBoundary
      ≡ false

    acquisitionNotResidualPayment :
      Follow.acquisitionEqualsResidualPayment
        Follow.canonicalLegalFollowProofSearchBoundary
      ≡ false

    runtimeNotLegalAuthority :
      Native.nativeCliCreatesLegalAuthority
        Native.canonicalNativeLegalFollowCliBoundary
      ≡ false

    providerFailureNotNegativeEvidence :
      Provider.providerFailureCountsAsNegativeLegalEvidence
        Provider.canonicalProviderFailureCalibration
      ≡ false

    governanceNotPoliticalAuthority :
      Governance.promotionCreatesPoliticalAuthority
        Governance.canonicalConsumerSafeGovernancePromotionBoundary
      ≡ false

open SensibLawGovernanceTOEPostconditions public

canonicalSensibLawGovernanceTOEPostconditions :
  SensibLawGovernanceTOEPostconditions
canonicalSensibLawGovernanceTOEPostconditions =
  record
    { semanticLegalAuthorityClosed =
        legalAuthorityRemainsClosed
    ; semanticAllAuthorityClosed =
        allSemanticAuthorityRemainsClosed
    ; expertAuthorityClosed =
        expertProductionAuthorityRemainsClosed
    ; candidateSourceNotAuthority =
        candidateLegalSourceDoesNotCreateAuthority
    ; semanticAdmissionNotLegalAuthority =
        semanticAdmissionCannotSubstituteForLegalAuthority
    ; legalAuthorityNotApplicability =
        legalAuthorityAloneDoesNotEstablishApplicability
    ; acquisitionNotResidualPayment =
        legalFollowAcquisitionDoesNotPayResidual
    ; runtimeNotLegalAuthority =
        nativeLegalFollowDoesNotCreateLegalAuthority
    ; providerFailureNotNegativeEvidence =
        providerFailureIsNotNegativeLegalEvidence
    ; governanceNotPoliticalAuthority =
        governancePromotionDoesNotCreatePoliticalAuthority
    }

record SensibLawGovernanceTOEZKPFrame : Set₁ where
  field
    O-objective :
      Semantic.SemanticPromotionPolicySurface

    R-risk :
      Authority.AuthorityNonPromotionBundle

    C-contract :
      Follow.LegalFollowProofSearchBoundary

    S-state :
      Native.NativeLegalFollowCliBoundary

    L-lattice :
      Legal.LegalSourceAuthorityBoundary

    P-policy :
      Governance.ConsumerSafeGovernancePromotionBoundary

    G-governance :
      Expert.ExpertProductionBoundary

    F-gap :
      SensibLawGovernanceTOEPostconditions

open SensibLawGovernanceTOEZKPFrame public

canonicalSensibLawGovernanceTOEZKPFrame :
  SensibLawGovernanceTOEZKPFrame
canonicalSensibLawGovernanceTOEZKPFrame =
  record
    { O-objective =
        Semantic.semanticPromotionPolicySurface
    ; R-risk =
        Semantic.semanticPromotionAuthorityBoundary
    ; C-contract =
        Follow.canonicalLegalFollowProofSearchBoundary
    ; S-state =
        Native.canonicalNativeLegalFollowCliBoundary
    ; L-lattice =
        Legal.canonicalLegalSourceAuthorityBoundary
    ; P-policy =
        Governance.canonicalConsumerSafeGovernancePromotionBoundary
    ; G-governance =
        Expert.canonicalExpertProductionBoundary
    ; F-gap =
        canonicalSensibLawGovernanceTOEPostconditions
    }

------------------------------------------------------------------------
-- Preconditions, invariants, postconditions.
------------------------------------------------------------------------

record SensibLawGovernanceTOEContract : Set₁ where
  field
    preconditions :
      SensibLawGovernanceTOEZKPFrame

    heuristicNonPromotionInvariant :
      ∀ heuristicFor heuristicAgainst target source →
      Semantic.promote
        (Semantic.heuristicCandidate
          heuristicFor heuristicAgainst target source)
      ≡ DASHI.Algebra.TetralemmaBridge.neither

    legalAuthorityClosureInvariant :
      legalAuthorityPromoted ≡ false

    postconditions :
      SensibLawGovernanceTOEPostconditions

open SensibLawGovernanceTOEContract public

canonicalSensibLawGovernanceTOEContract :
  SensibLawGovernanceTOEContract
canonicalSensibLawGovernanceTOEContract =
  record
    { preconditions =
        canonicalSensibLawGovernanceTOEZKPFrame
    ; heuristicNonPromotionInvariant =
        heuristicEvidenceCannotPromote
    ; legalAuthorityClosureInvariant =
        legalAuthorityRemainsClosed
    ; postconditions =
        canonicalSensibLawGovernanceTOEPostconditions
    }
