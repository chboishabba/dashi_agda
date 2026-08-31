module DASHI.Base369StratifiedReceptionCrossPollinationValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact as Fibre
import DASHI.Governance.CollectiveMemoryReceptionHistoryExact as Reception

edgeStratumDoesNotRecoverSector :
  INF.FactorsThrough Fibre.edgeStratumSurface Fibre.edgeSectorSurface → ⊥
edgeStratumDoesNotRecoverSector = Fibre.edgeStratumCannotRecoverSectorClass

cornerStratumDoesNotRecoverSector :
  INF.FactorsThrough Fibre.cornerStratumSurface Fibre.cornerSectorSurface → ⊥
cornerStratumDoesNotRecoverSector = Fibre.cornerStratumCannotRecoverSectorClass

sameVocabularyDoesNotRecoverMeaning :
  INF.FactorsThrough Reception.vocabularySurface Reception.semanticHistory → ⊥
sameVocabularyDoesNotRecoverMeaning =
  Reception.sameVocabularyCannotRecoverSemanticHistory

sameVocabularyDoesNotRecoverInstitution :
  INF.FactorsThrough Reception.institutionalVocabularySurface Reception.institutionalHistory → ⊥
sameVocabularyDoesNotRecoverInstitution =
  Reception.sameVocabularyCannotRecoverInstitutionalHistory

sameUseDoesNotRecoverAuthority :
  INF.FactorsThrough Reception.presentUseSurface Reception.authorityHistory → ⊥
sameUseDoesNotRecoverAuthority = Reception.presentUseCannotRecoverAuthorityHistory

mergedCollectiveMemoryBoundaryRetained :
  Reception.mergedCollectiveMemoryDoesNotEqualInstitutionalContinuity ≡ refl
mergedCollectiveMemoryBoundaryRetained = refl
