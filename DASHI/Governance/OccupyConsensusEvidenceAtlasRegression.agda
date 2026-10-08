module DASHI.Governance.OccupyConsensusEvidenceAtlasRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Evidence

burdenEvidencePresent :
  Evidence.documentedBurdenEvidencePresent Evidence.canonicalOccupyConsensusEvidenceBoundary ≡ true
burdenEvidencePresent = refl

benefitEvidencePresent :
  Evidence.documentedDeliberativeBenefitEvidencePresent Evidence.canonicalOccupyConsensusEvidenceBoundary ≡ true
benefitEvidencePresent = refl

coordinationEvidencePresent :
  Evidence.documentedCoordinationMechanismEvidencePresent Evidence.canonicalOccupyConsensusEvidenceBoundary ≡ true
coordinationEvidencePresent = refl

noUniversalFailureLaw :
  Evidence.evidenceProvesUniversalConsensusFailure Evidence.canonicalOccupyConsensusEvidenceBoundary ≡ false
noUniversalFailureLaw = refl

noQuantitativeSizeLaw :
  Evidence.evidenceProvesQuantitativeGroupSizeScalingLaw Evidence.canonicalOccupyConsensusEvidenceBoundary ≡ false
noQuantitativeSizeLaw = refl
