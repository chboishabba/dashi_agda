module DASHI.Core.GeneralizedRoleGovernanceGuards where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens
open import DASHI.Core.FormalStructureKind

-- Empty promotion types make the non-claims executable rather than comments.
data UniversalDomainTruth : Set where

data AutomaticCrossDomainTransport : Set where

data SharedHamiltonianForAllDomains : Set where

data SharedInvariantForAllDomains : Set where

data ObservableRecoversHiddenCarrier : Set where

data SemioticMeaningIsPhysicalCause : Set where

data DocumentationIsCompliance : Set where

data PositiveMeasureIsConstruction : Set where

data FeedbackIsDemocraticLegitimacy : Set where

noUniversalDomainTruth : UniversalDomainTruth → ⊥
noUniversalDomainTruth ()

noAutomaticCrossDomainTransport : AutomaticCrossDomainTransport → ⊥
noAutomaticCrossDomainTransport ()

noSharedHamiltonianForAllDomains : SharedHamiltonianForAllDomains → ⊥
noSharedHamiltonianForAllDomains ()

noSharedInvariantForAllDomains : SharedInvariantForAllDomains → ⊥
noSharedInvariantForAllDomains ()

noObservableRecovery : ObservableRecoversHiddenCarrier → ⊥
noObservableRecovery ()

noSemioticCausationPromotion : SemioticMeaningIsPhysicalCause → ⊥
noSemioticCausationPromotion ()

noPolicyToCompliancePromotion : DocumentationIsCompliance → ⊥
noPolicyToCompliancePromotion ()

noExistenceToConstructionPromotion : PositiveMeasureIsConstruction → ⊥
noExistenceToConstructionPromotion ()

noFeedbackToLegitimacyPromotion : FeedbackIsDemocraticLegitimacy → ⊥
noFeedbackToLegitimacyPromotion ()

-- Shared labels provide only a comparison surface.  A bridge is still needed.
roleLabelComparisonSurface : FormalRole → FormalRole
roleLabelComparisonSurface r = r

lensLabelComparisonSurface : ProofLens → ProofLens
lensLabelComparisonSurface l = l

structureLabelComparisonSurface : FormalStructureKind → FormalStructureKind
structureLabelComparisonSurface s = s
