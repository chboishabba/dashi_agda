module DASHI.Interop.SensibLawNatSourceDiscoveryValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SensibLawNatSourceDiscoveryExact as Discovery
import DASHI.Interop.SensibLawNatSourceLineageExact as Lineage

failedLocatorMayScheduleDiscovery :
  Discovery.NatSourceDiscoveryBoundary.failedLocatorMayScheduleDiscovery
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
failedLocatorMayScheduleDiscovery = refl

providerIsNotSemanticAuthority :
  Discovery.NatSourceDiscoveryBoundary.discoveryProviderIsSemanticallyPrivileged
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
providerIsNotSemanticAuthority = refl

candidateDoesNotPayIdentity :
  Discovery.NatSourceDiscoveryBoundary.discoveryCandidatePaysSameSourceIdentity
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
candidateDoesNotPayIdentity = refl

rankDoesNotPaySourceSupport :
  Discovery.NatSourceDiscoveryBoundary.providerRankPaysSourceSupport
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
rankDoesNotPaySourceSupport = refl

snippetDoesNotPaySourceSupport :
  Discovery.NatSourceDiscoveryBoundary.providerSnippetPaysSourceSupport
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
snippetDoesNotPaySourceSupport = refl

identityRequiresReceipt :
  Discovery.NatSourceDiscoveryBoundary.sameSourceIdentityRequiresSeparateReceipt
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
identityRequiresReceipt = refl

sameSourceIsPositive :
  Discovery.NatSourceDiscoveryBoundary.sameSourceIdentityMapsPositive
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
sameSourceIsPositive = refl

differentSourceIsNegative :
  Discovery.NatSourceDiscoveryBoundary.differentSourceMapsNegative
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
differentSourceIsNegative = refl

unresolvedIdentityIsZero :
  Discovery.NatSourceDiscoveryBoundary.unresolvedIdentityMapsZero
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
unresolvedIdentityIsZero = refl

differentCandidateDoesNotEraseSource :
  Discovery.NatSourceDiscoveryBoundary.differentCandidateMeansSourceAbsent
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
differentCandidateDoesNotEraseSource = refl

discoveryFailureDoesNotEraseSource :
  Discovery.NatSourceDiscoveryBoundary.discoveryFailureMeansSourceAbsent
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
discoveryFailureDoesNotEraseSource = refl

sameSourceIdentityDoesNotPaySourceSupport :
  Discovery.NatSourceDiscoveryBoundary.sameSourceIdentityPaysSourceSupport
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
sameSourceIdentityDoesNotPaySourceSupport = refl

sameSourceIdentityDoesNotCreateAuthority :
  Discovery.NatSourceDiscoveryBoundary.sameSourceIdentityCreatesAuthority
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ false
sameSourceIdentityDoesNotCreateAuthority = refl

admittedAlternateMayReenterTransport :
  Discovery.NatSourceDiscoveryBoundary.admittedAlternateLocatorMayReenterExistingFetch
    Discovery.canonicalNatSourceDiscoveryBoundary ≡ true
admittedAlternateMayReenterTransport = refl

differentSourceMayStillCarryLineage :
  Lineage.NatSourceLineageBoundary.differentSourceMayStillCarryUsefulLineage
    Lineage.canonicalNatSourceLineageBoundary ≡ true
differentSourceMayStillCarryLineage = refl

sourceOfSourceDoesNotPayIdentity :
  Lineage.NatSourceLineageBoundary.sourceOfSourcePaysSameSourceIdentity
    Lineage.canonicalNatSourceLineageBoundary ≡ false
sourceOfSourceDoesNotPayIdentity = refl

sourceOfSourceDoesNotReenterTransport :
  Lineage.NatSourceLineageBoundary.sourceOfSourceMayReenterAlternateFetch
    Lineage.canonicalNatSourceLineageBoundary ≡ false
sourceOfSourceDoesNotReenterTransport = refl

sourceLineageMayRefineQueries :
  Lineage.NatSourceLineageBoundary.sourceLineageMayRefineDiscoveryQueries
    Lineage.canonicalNatSourceLineageBoundary ≡ true
sourceLineageMayRefineQueries = refl

sourceLineageDoesNotPaySupport :
  Lineage.NatSourceLineageBoundary.sourceLineagePaysSourceSupport
    Lineage.canonicalNatSourceLineageBoundary ≡ false
sourceLineageDoesNotPaySupport = refl
