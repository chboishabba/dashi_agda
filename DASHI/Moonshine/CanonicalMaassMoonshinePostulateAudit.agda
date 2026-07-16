module DASHI.Moonshine.CanonicalMaassMoonshinePostulateAudit where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

------------------------------------------------------------------------
-- The audit is separate from the theorem package.  It classifies every
-- terminal dependency without converting a citation or unresolved obligation
-- into a proof witness.

data TheoremAuthorityStatus : Set where
  derivedInDASHI : TheoremAuthorityStatus
  verifiedComputation : TheoremAuthorityStatus
  importedMachineChecked : TheoremAuthorityStatus
  citationOnly : TheoremAuthorityStatus
  unresolved : TheoremAuthorityStatus

Tracked : TheoremAuthorityStatus → Set
Tracked unresolved = ⊥
Tracked _ = ⊤

record MaassMoonshineFieldAudit : Set where
  field
    finiteSampling : TheoremAuthorityStatus
    hejhalContraction : TheoremAuthorityStatus
    validatedBesselAndTailBounds : TheoremAuthorityStatus
    residualToSpectralEnclosure : TheoremAuthorityStatus
    spectralMultiplicityOne : TheoremAuthorityStatus
    monsterAction : TheoremAuthorityStatus
    exactCharacterTable : TheoremAuthorityStatus
    gradedTraceToMcKayThompson : TheoremAuthorityStatus
    namedRestrictedBridge : TheoremAuthorityStatus
    residualNaturality : TheoremAuthorityStatus
    refinementPersistence : TheoremAuthorityStatus

NoUntrackedEssentialAssumptions : MaassMoonshineFieldAudit → Set
NoUntrackedEssentialAssumptions audit =
  Tracked (MaassMoonshineFieldAudit.finiteSampling audit)
  × Tracked (MaassMoonshineFieldAudit.hejhalContraction audit)
  × Tracked (MaassMoonshineFieldAudit.validatedBesselAndTailBounds audit)
  × Tracked (MaassMoonshineFieldAudit.residualToSpectralEnclosure audit)
  × Tracked (MaassMoonshineFieldAudit.spectralMultiplicityOne audit)
  × Tracked (MaassMoonshineFieldAudit.monsterAction audit)
  × Tracked (MaassMoonshineFieldAudit.exactCharacterTable audit)
  × Tracked (MaassMoonshineFieldAudit.gradedTraceToMcKayThompson audit)
  × Tracked (MaassMoonshineFieldAudit.namedRestrictedBridge audit)
  × Tracked (MaassMoonshineFieldAudit.residualNaturality audit)
  × Tracked (MaassMoonshineFieldAudit.refinementPersistence audit)
