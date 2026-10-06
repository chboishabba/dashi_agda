module DASHI.Governance.FederatedGovernanceEvidenceSourceRegistryRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Governance.FederatedGovernanceEvidenceSourceRegistryExact as Source

boloAuthorPinned :
  Registry.authorsOrInstitution Source.boloBolo30thSource ≡ "p.m."
boloAuthorPinned = refl

bookchinTitlePinned :
  Registry.title Source.bookchinConfederalismSource ≡ "The Meaning of Confederalism"
bookchinTitlePinned = refl

minDOIPinned :
  Registry.doiOrIdentifier Source.min2015Source ≡ "10.1111/cccr.12074"
minDOIPinned = refl

savioDOIPinned :
  Registry.doiOrIdentifier Source.savio2015Source ≡ "10.1080/10282580.2015.1005509"
savioDOIPinned = refl

pollettaHobanDOIPinned :
  Registry.doiOrIdentifier Source.pollettaHoban2016Source ≡ "10.5964/jspp.v4i1.524"
pollettaHobanDOIPinned = refl

sameThemeDoesNotMergeSources :
  Source.sameGovernanceThemeCollapsesProvenance Source.canonicalGovernanceEvidenceRegistryBoundary ≡ false
sameThemeDoesNotMergeSources = refl
