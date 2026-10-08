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

occupyArchiveDatasetDOIPinned :
  Registry.doiOrIdentifier Source.kinnaPrichard2019ArchiveSource
  ≡ "10.5255/UKDA-SN-853247"
occupyArchiveDatasetDOIPinned = refl

hwangGuynesDOIPinned :
  Registry.doiOrIdentifier Source.hwangGuynes1994Source ≡ "10.1016/0378-7206(94)90092-2"
hwangGuynesDOIPinned = refl

millerVanbergDOIPinned :
  Registry.doiOrIdentifier Source.millerVanberg2015Source ≡ "10.1016/j.ejpoleco.2014.09.005"
millerVanbergDOIPinned = refl

mckoyDOIPinned :
  Registry.doiOrIdentifier Source.mckoyEtAl2012Source ≡ "10.1016/j.protcy.2012.09.052"
mckoyDOIPinned = refl

luYuanMcLeodDOIPinned :
  Registry.doiOrIdentifier Source.luYuanMcLeod2012Source ≡ "10.1177/1088868311417243"
luYuanMcLeodDOIPinned = refl

sameThemeDoesNotMergeSources :
  Source.sameGovernanceThemeCollapsesProvenance Source.canonicalGovernanceEvidenceRegistryBoundary ≡ false
sameThemeDoesNotMergeSources = refl
