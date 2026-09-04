module DASHI.Analysis.NonArchimedeanSpectralProofSearchPruningBidiExact where

------------------------------------------------------------------------
-- PROOF-SEARCH PRUNING AFTER EXISTING-MACHINERY REUSE
--
-- User-level assumption for this tranche: DASHI already contains the generic
-- machinery we need.  Therefore reverse search must target only source-specific
-- instantiations and receipts, not rebuild generic codecs, intertwiners, or the
-- monomial power reduction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanTwistedBlockReductionBidiExact as Reduction


data SearchAction : Set where
  instantiateExistingIntertwiner : SearchAction
  recoverConcreteGroupLabelling : SearchAction
  attachConcretePeriodReceipt : SearchAction
  attachConcreteOrbitWeightReceipt : SearchAction
  invokeOwnedGenericPowerReduction : SearchAction

  rebuildGenericIntertwinerKernel : SearchAction
  rebuildGenericSpectralCodec : SearchAction
  reproveGenericMonomialPower : SearchAction
  identifyDyadicCarrierWithTriadicCarrier : SearchAction


data SearchStatus : Set where
  downstream : SearchStatus
  pruned : SearchStatus
  forbidden : SearchStatus

searchStatus : SearchAction → SearchStatus
searchStatus instantiateExistingIntertwiner = downstream
searchStatus recoverConcreteGroupLabelling = downstream
searchStatus attachConcretePeriodReceipt = downstream
searchStatus attachConcreteOrbitWeightReceipt = downstream
searchStatus invokeOwnedGenericPowerReduction = downstream

searchStatus rebuildGenericIntertwinerKernel = pruned
searchStatus rebuildGenericSpectralCodec = pruned
searchStatus reproveGenericMonomialPower = pruned
searchStatus identifyDyadicCarrierWithTriadicCarrier = forbidden

rebuildIntertwinerPruned :
  searchStatus rebuildGenericIntertwinerKernel ≡ pruned
rebuildIntertwinerPruned = refl

rebuildCodecPruned :
  searchStatus rebuildGenericSpectralCodec ≡ pruned
rebuildCodecPruned = refl

reprovePowerPruned :
  searchStatus reproveGenericMonomialPower ≡ pruned
reprovePowerPruned = refl

crossRadixCarrierIdentificationForbidden :
  searchStatus identifyDyadicCarrierWithTriadicCarrier ≡ forbidden
crossRadixCarrierIdentificationForbidden = refl

------------------------------------------------------------------------
-- Highest-alpha path: instantiate -> label -> period/weight -> reduction.
------------------------------------------------------------------------

highestAlphaPath : List SearchAction
highestAlphaPath =
  instantiateExistingIntertwiner ∷
  recoverConcreteGroupLabelling ∷
  attachConcretePeriodReceipt ∷
  attachConcreteOrbitWeightReceipt ∷
  invokeOwnedGenericPowerReduction ∷
  []

record ProofSearchPruningBoundary : Set where
  constructor proofSearchPruningBoundary
  field
    infrastructureSearchClosed : Bool
    sourceSpecificInstantiationRemains : Bool
    genericPowerReductionAlreadyOwned : Bool
    strongerSpatialClaimNeedsSameObjectInstantiation : Bool

canonicalProofSearchPruningBoundary : ProofSearchPruningBoundary
canonicalProofSearchPruningBoundary =
  proofSearchPruningBoundary true true true true
