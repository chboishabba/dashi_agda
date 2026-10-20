module DASHI.Governance.BoloBoloCausalJointPromotionRegression where

-- RED-first contract: the production owner must distinguish
--   repeated validated association
-- from
--   causally identified coordination advantage,
-- and must separately gate any claim that nested governance causally improves
-- realised non-domination.

import DASHI.Governance.BoloBoloCausalJointPromotionExact as Joint

coordinationCausalGateRequired :
  Joint.coordinationCausalIdentificationRequired
    Joint.canonicalCausalJointPromotionBoundary ≡ true
coordinationCausalGateRequired = refl

nonDominationCausalGateSeparate :
  Joint.nonDominationCausalEffectRequiresSeparateIdentification
    Joint.canonicalCausalJointPromotionBoundary ≡ true
nonDominationCausalGateSeparate = refl

jointStateDoesNotCreateNonDominationCausalEffect :
  Joint.jointStateCertificateAutomaticallyProvesNonDominationCausalEffect
    Joint.canonicalCausalJointPromotionBoundary ≡ false
jointStateDoesNotCreateNonDominationCausalEffect = refl

coordinationIdentificationDoesNotIdentifyNonDomination :
  Joint.coordinationIdentificationAutomaticallyIdentifiesNonDominationEffect
    Joint.canonicalCausalJointPromotionBoundary ≡ false
coordinationIdentificationDoesNotIdentifyNonDomination = refl
