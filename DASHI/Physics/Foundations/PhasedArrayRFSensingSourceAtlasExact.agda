module DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Attribution coordinates only.  Community/video/forum rows generate leads;
-- academic rows pay only the source-bounded technical statements named in
-- their relationships.  No citation imports a DASHI theorem or authority.
------------------------------------------------------------------------

techIngredientsLead : Source.AttributedSource
techIngredientsLead = Source.mkNoDOISource
  "Tech Ingredients"
  "Tech Ingredients YouTube channel — microwave/radar demonstrations"
  "YouTube"
  "2026 snapshot"
  "https://www.youtube.com/@TechIngredients"
  Source.communitySource
  "community/practitioner lead for microwave, radar, attenuation and RF terminology; not primary authority for phased-array or through-wall sensing claims"
  Source.publicAttribution

rfPosePrimary : Source.AttributedSource
rfPosePrimary = Source.mkNoDOISource
  "Mingmin Zhao; Tianhong Li; Mohammad Abu Alsheikh; Yonglong Tian; Hang Zhao; Antonio Torralba; Dina Katabi"
  "Through-Wall Human Pose Estimation Using Radio Signals"
  "CVPR 2018 / MIT CSAIL RF-Pose project"
  "2018"
  "https://rfpose.csail.mit.edu/"
  Source.academicArticleSource
  "primary research source for the bounded claim that radio-frequency observations can support human-pose inference through walls/occlusions; not exact identity, intent, or surveillance authority"
  Source.publicAttribution

csiModelSurvey : Source.AttributedSource
csiModelSurvey = Source.mkDOISource
  "Zhengjie Wang; Zehua Huang; Chengming Zhang; Wenwen Dou; Yinjing Guo; Da Chen"
  "CSI-based human sensing using model-based approaches: a survey"
  "Journal of Computational Design and Engineering 8(2), 510-523"
  "2021"
  "10.1093/jcde/qwab003"
  "https://doi.org/10.1093/jcde/qwab003"
  Source.academicArticleSource
  "survey source for Wi-Fi channel-state-information human sensing, including phase/AoA/model-based observation and through-wall RF examples"
  Source.publicAttribution

csiWifiSurvey : Source.AttributedSource
csiWifiSurvey = Source.mkDOISource
  "Yongsen Ma; Gang Zhou; Shuangquan Wang"
  "WiFi Sensing with Channel State Information: A Survey"
  "ACM Computing Surveys 52(3)"
  "2019"
  "10.1145/3310194"
  "https://doi.org/10.1145/3310194"
  Source.academicArticleSource
  "survey source for CSI as a sensing observation of multipath, attenuation and phase changes; citation does not imply exact reconstruction"
  Source.publicAttribution

dcsCommunityLead : Source.AttributedSource
dcsCommunityLead = Source.mkNoDOISource
  "DCS community contributors"
  "Any plans to make RWR more realistic and less accurate?"
  "DCS / Eagle Dynamics community forum"
  "2026 snapshot"
  "https://forum.dcs.world/topic/305917-any-plans-to-make-rwr-more-realistic-and-less-accurate/"
  Source.communitySource
  "lead-generation source for amplitude-comparison versus phase/interferometric RWR terminology; requires primary-source payment before promotion to technical fact"
  Source.publicAttribution

warThunderCommunityLead : Source.AttributedSource
warThunderCommunityLead = Source.mkNoDOISource
  "War Thunder community contributors"
  "Phased Array Radars ACM Mode Scan Speeds"
  "War Thunder official forum"
  "2026 snapshot"
  "https://forum.warthunder.com/t/phased-array-radars-acm-mode-scan-speeds/240549"
  Source.communitySource
  "lead-generation source for mechanically oriented versus electronically steered phased-array terminology; not technical authority"
  Source.publicAttribution

hackadayConsumerWifiLead : Source.AttributedSource
hackadayConsumerWifiLead = Source.mkNoDOISource
  "Donald Papp / Hackaday"
  "Make Your Own ESP32-Based Person Sensor, No Special Hardware Needed"
  "Hackaday"
  "2026"
  "https://hackaday.com/2026/01/28/make-your-own-esp32-based-person-sensor-no-special-hardware-needed/"
  Source.communitySource
  "lead showing commodity ESP32 Wi-Fi CSI used for person/motion sensing and reported wall penetration; primary literature still pays general technical claims"
  Source.publicAttribution

hackadaySDRPassiveRadarLead : Source.AttributedSource
hackadaySDRPassiveRadarLead = Source.mkNoDOISource
  "Juha Vierinen / Hackaday"
  "Building Your Own SDR-based Passive Radar On A Shoestring"
  "Hackaday"
  "2015"
  "https://hackaday.com/2015/06/05/building-your-own-sdr-based-passive-radar-on-a-shoestring/"
  Source.communitySource
  "lead showing passive-radar experimentation with inexpensive RTL-SDR receivers and existing illuminators; not operational surveillance authority"
  Source.publicAttribution

hackadayPhasedArrayThroughWallLead : Source.AttributedSource
hackadayPhasedArrayThroughWallLead = Source.mkNoDOISource
  "Gregory L. Charvat / Hackaday"
  "Build A Phased-Array Radar In Your Garage That Sees Through Walls"
  "Hackaday"
  "2015"
  "https://hackaday.com/2015/04/07/build-a-phased-array-radar-in-your-garage-that-sees-through-walls/"
  Source.communitySource
  "lead connecting low-cost phased-array experimentation, Wi-Fi-band antennas and through-wall radar demonstrations; underlying technical papers remain the acquisition target"
  Source.publicAttribution

phasedArrayRFSensingAtlas : Source.AttributedSourceAtlas
phasedArrayRFSensingAtlas = Source.mkSourceAtlas
  "phased-array / RF-sensing bounded source atlas"
  "DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact"
  (techIngredientsLead ∷ rfPosePrimary ∷ csiModelSurvey ∷ csiWifiSurvey ∷ dcsCommunityLead ∷ warThunderCommunityLead ∷ hackadayConsumerWifiLead ∷ hackadaySDRPassiveRadarLead ∷ hackadayPhasedArrayThroughWallLead ∷ [])
  "community leads remain acquisition leads; academic sources pay only bounded observation claims; all system identity, exact hardware provenance, operational use, and authority claims remain separate"
