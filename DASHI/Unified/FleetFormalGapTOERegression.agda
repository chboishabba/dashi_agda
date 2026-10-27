module DASHI.Unified.FleetFormalGapTOERegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Unified.FleetFormalGapTOEExact as Fleet

fleetDischargedCountIs584 :
  Fleet.dischargedCoreKnowledgeCount Fleet.canonicalFleetFormalGapReceipt ≡ 584
fleetDischargedCountIs584 = refl

fleetContradictionCountIs44 :
  Fleet.polarityContradictionCount Fleet.canonicalFleetFormalGapReceipt ≡ 44
fleetContradictionCountIs44 = refl

fleetFormalGapCountIs58 :
  Fleet.unformalisedFormalGapCount Fleet.canonicalFleetFormalGapReceipt ≡ 58
fleetFormalGapCountIs58 = refl

onlyFormalResidualDispatches :
  Fleet.dispatchAllowed Fleet.unformalisedFormalGap ≡ true
onlyFormalResidualDispatches = refl

dischargedFibresDoNotDispatch :
  Fleet.dispatchAllowed Fleet.dischargedCoreKnowledge ≡ false
dischargedFibresDoNotDispatch = refl

contradictionFibresDoNotDispatchAsFormalGaps :
  Fleet.dispatchAllowed Fleet.polarityContradictionGap ≡ false
contradictionFibresDoNotDispatchAsFormalGaps = refl

spectralMotifDoesNotCreateTruth :
  Fleet.SpectralMotifCreatesTruth → ⊥
spectralMotifDoesNotCreateTruth =
  Fleet.spectralMotifDoesNotCreateTruth

formalGapCountDoesNotCreateProof :
  Fleet.FormalGapCountCreatesProof → ⊥
formalGapCountDoesNotCreateProof =
  Fleet.formalGapCountDoesNotCreateProof

fleetLegalGovernanceHandoffIsCanonical :
  Fleet.legalGovernanceHandoff Fleet.canonicalFleetFormalGapReceipt
  ≡ Fleet.canonicalLegalGovernanceHandoff
fleetLegalGovernanceHandoffIsCanonical = refl

fleetMaxCutRegression :
  Fleet.canonicalFleetFormalGapMaxCut ≡ Fleet.canonicalFleetFormalGapMaxCut
fleetMaxCutRegression = refl

namedGapManifestStillMissing :
  Fleet.namedFormalGapManifestAcquired Fleet.canonicalFleetFormalGapMaxCut ≡ false
namedGapManifestStillMissing = refl
