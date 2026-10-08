module DASHI.Governance.BoloBoloComparatorInstitutionalVersioningRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloComparatorInstitutionalVersioningExact as Versioning

historicalCouncilCountPinned :
  Versioning.historicalCouncilMemberCount Versioning.canonicalPortoAlegreHistoricalVersion ≡ 44
historicalCouncilCountPinned = refl

currentAssemblyStreamsPinned :
  Versioning.currentAssemblyStreamCount Versioning.canonicalPortoAlegreCurrent2026Version ≡ 23
currentAssemblyStreamsPinned = refl

currentCouncillorCountPinned :
  Versioning.currentCouncillorCount Versioning.canonicalPortoAlegreCurrent2026Version ≡ 92
currentCouncillorCountPinned = refl

versionWitnessRequired :
  Versioning.transportMustNameInstitutionalVersion Versioning.canonicalComparatorVersioningBoundary ≡ true
versionWitnessRequired = refl

noSilentSplice :
  Versioning.historicalAndCurrentCoordinatesMayBeSplicedWithoutVersionWitness Versioning.canonicalComparatorVersioningBoundary ≡ false
noSilentSplice = refl
