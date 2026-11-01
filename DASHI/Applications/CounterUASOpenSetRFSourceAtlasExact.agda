module DASHI.Applications.CounterUASOpenSetRFSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ACADEMIC OPEN-SET RF SOURCE ATLAS
--
-- These papers support the general scientific distinction between closed-set
-- identification and open-set recognition of previously unseen RF/UAV classes.
-- They do not validate DroneShield, reproduce RfAI-3, or import vendor claims.
------------------------------------------------------------------------

hongLiangWangYueLi2026 : Source.AttributedSource
hongLiangWangYueLi2026 =
  Source.mkDOISource
    "Jiangfeng Hong; Jiakai Liang; Chao Wang; Keqiang Yue; Wenjun Li"
    "Open set recognition for drone based on deep metric learning"
    "Physical Communication 75, 103030"
    "2026"
    "10.1016/j.phycom.2026.103030"
    "https://doi.org/10.1016/j.phycom.2026.103030"
    Source.academicArticleSource
    "academic source showing that closed-set UAV RF identification is inadequate for unidentified classes and that open-set recognition explicitly separates known-class identification from handling previously unseen UAV RF classes; not a DroneShield product validation"
    Source.publicAttribution

gaoZengChenCaiJinMatthaiou2026 : Source.AttributedSource
gaoZengChenCaiJinMatthaiou2026 =
  Source.mkDOISource
    "Ning Gao; Tianrui Zeng; Bowen Chen; Donghong Cai; Shi Jin; Michail Matthaiou"
    "Multi-Domain Supervised Contrastive Learning for UAV Radio-Frequency Open-Set Recognition"
    "IEEE Journal on Selected Areas in Communications 44, 4083-4098"
    "2026"
    "10.1109/JSAC.2026.3669136"
    "https://doi.org/10.1109/JSAC.2026.3669136"
    Source.academicArticleSource
    "academic source for UAV RF open-set recognition that distinguishes performance on known closed-set classes from recognition of unknown samples; supports the general known/unknown boundary but does not establish RfAI-3 implementation details"
    Source.publicAttribution

counterUASOpenSetRFSources : List Source.AttributedSource
counterUASOpenSetRFSources =
  hongLiangWangYueLi2026 ∷
  gaoZengChenCaiJinMatthaiou2026 ∷
  []

counterUASOpenSetRFSourceAtlas : Source.AttributedSourceAtlas
counterUASOpenSetRFSourceAtlas =
  Source.mkSourceAtlas
    "counter-UAS open-set RF academic sources"
    "DASHI.Applications.CounterUASOpenSetRFSourceAtlasExact"
    counterUASOpenSetRFSources
    "academic support for the closed-set/open-set distinction in UAV radio-frequency recognition; does not prove any vendor's proprietary implementation, field performance, threat classification, or mitigation authority"

counterUASOpenSetRFSourceAtlasCreatesAuthority : Bool
counterUASOpenSetRFSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority counterUASOpenSetRFSourceAtlas

counterUASOpenSetRFSourceAtlasCreatesAuthorityIsFalse :
  counterUASOpenSetRFSourceAtlasCreatesAuthority ≡ false
counterUASOpenSetRFSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse counterUASOpenSetRFSourceAtlas

record OpenSetRFAttributionBoundary : Set where
  constructor openSetRFAttributionBoundary
  field
    academicOpenSetResultEqualsRfAI3Implementation : Bool
    academicOpenSetResultEqualsRfAI3ImplementationIsFalse :
      academicOpenSetResultEqualsRfAI3Implementation ≡ false
    vendorOpenSetClaimEqualsAcademicReplication : Bool
    vendorOpenSetClaimEqualsAcademicReplicationIsFalse :
      vendorOpenSetClaimEqualsAcademicReplication ≡ false

canonicalOpenSetRFAttributionBoundary : OpenSetRFAttributionBoundary
canonicalOpenSetRFAttributionBoundary =
  openSetRFAttributionBoundary false refl false refl
