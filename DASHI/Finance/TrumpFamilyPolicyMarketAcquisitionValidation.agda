module DASHI.Finance.TrumpFamilyPolicyMarketAcquisitionValidation where

import DASHI.Finance.TrumpFamilyPolicyMarketSourceAtlasExact as Policy

------------------------------------------------------------------------
-- RED regression: ownership, policy text and independent synthesis must remain
-- separate evidence edges, with knowledge/influence/realized-benefit unpaid.
------------------------------------------------------------------------

grabAGunTriadIsPresent = Policy.canonicalGrabAGunPolicyMarketTriad
policySourceIsPrimary = Policy.grabAGunATFNonOTCProposal
independentCounterevidenceIsRetained = Policy.grabAGunReutersPolicyExposure
knowledgeIsStillUnpaid = Policy.grabAGunKnowledgeBoundary
