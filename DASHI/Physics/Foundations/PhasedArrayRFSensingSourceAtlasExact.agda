module DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Attribution coordinates only.  Community/video/forum rows generate leads;
-- academic, archival, government and patent rows pay only the source-bounded
-- technical or historical statements named in their relationships.  No
-- citation imports a DASHI theorem or creates authority.
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

spotFiAoAPrimary : Source.AttributedSource
spotFiAoAPrimary = Source.mkNoDOISource
  "Manikanta Kotaru; Kiran Joshi; Dinesh Bharadia; Sachin Katti"
  "SpotFi: Decimeter Level Localization Using WiFi"
  "ACM SIGCOMM 2015"
  "2015"
  "https://web.stanford.edu/~skatti/pubs/sigcomm15-spotfi.pdf"
  Source.academicArticleSource
  "primary research source for the bounded claim that commodity Wi-Fi CSI from a small antenna array can support angle-of-arrival estimation of multipath components; not a claim that coarse CSI amplitude alone determines angle or exact world state"
  Source.publicAttribution

wifiCSIAoAToFPrimary : Source.AttributedSource
wifiCSIAoAToFPrimary = Source.mkDOISource
  "Afaz Uddin Ahmed; Reza Arablouei; Frank de Hoog; Brano Kusy; Raja Jurdak; Neil Bergmann"
  "Estimating Angle-of-Arrival and Time-of-Flight for Multipath Components Using WiFi Channel State Information"
  "Sensors 18(6):1753"
  "2018"
  "10.3390/s18061753"
  "https://doi.org/10.3390/s18061753"
  Source.academicArticleSource
  "primary research source for estimating multipath AoA and time-of-flight from Wi-Fi CSI; pays only the source-bounded measurement relationship, not hardware identity, exact emitter identity, or operational authority"
  Source.publicAttribution

belliniTosiPatentPrimary : Source.AttributedSource
belliniTosiPatentPrimary = Source.mkNoDOISource
  "Ettore Bellini; Alessandro Tosi"
  "Improvements in Directed Wireless Telegraphy"
  "GB190904801A patent specification"
  "1909"
  "https://patents.google.com/patent/GB190904801A/en"
  (Source.namedSourceKind "patent")
  "primary patent source for the Bellini-Tosi directed-wireless lineage; pays only the historical apparatus/system claim represented by the specification"
  Source.publicAttribution

belliniTosiNatureHistorical : Source.AttributedSource
belliniTosiNatureHistorical = Source.mkDOISource
  "O. F. B."
  "Radio Direction Finding by Reception"
  "Nature 112, 690-692"
  "1923"
  "10.1038/112690a0"
  "https://doi.org/10.1038/112690a0"
  Source.academicArticleSource
  "contemporary historical source distinguishing Bellini-Tosi, single-frame and Robinson reception direction-finding systems; does not identify the user's observed instrument"
  Source.publicAttribution

belliniTosiOxfordArchive : Source.AttributedSource
belliniTosiOxfordArchive = Source.mkNoDOISource
  "History of Science Museum, Oxford"
  "Bellini-Tosi Direction Finder, by Bellini & Tosi, Paris, 1907 — inventory 14937"
  "Marconi Collection catalogue"
  "1907 object / catalogue snapshot"
  "https://www.mhs.ox.ac.uk/marconi/collection/cataloguecba9.html?invnum=14937&mode=documents"
  Source.archivalSource
  "archival object identity and inscription source for an early Bellini-Tosi goniometer/direction-finder; comparison source only, not proof that an observed external instrument is the same object"
  Source.publicAttribution

belliniTosiMuseumMechanism : Source.AttributedSource
belliniTosiMuseumMechanism = Source.mkNoDOISource
  "Museo Nazionale della Scienza e della Tecnologia Leonardo da Vinci / Regione Lombardia"
  "The Wireless Direction Finder - Marconi Bellini Tosi System"
  "Lombardia Beni Culturali scientific and technological heritage catalogue"
  "catalogue record"
  "https://www.lombardiabeniculturali.it/scienza-tecnologia/schede/ST050-00091/"
  Source.institutionalSource
  "institutional museum source for the bounded mechanism description: orthogonal field coils and a rotatable search coil used to measure direction; not exact provenance of the user's observed instrument"
  Source.publicAttribution

phasedArrayMonopulsePrimary : Source.AttributedSource
phasedArrayMonopulsePrimary = Source.mkDOISource
  "Xuemin Cao; Zhenhai Xu"
  "Four-channel monopulse angle estimation for phased array radar with elliptical plane"
  "The Journal of Engineering"
  "2019"
  "10.1049/joe.2019.0660"
  "https://doi.org/10.1049/joe.2019.0660"
  Source.academicArticleSource
  "primary research source for phased-array monopulse angle estimation and sum/difference-channel angular observation; does not imply that every phased array uses monopulse or that angle observation determines exact target state"
  Source.publicAttribution

phasedArrayGovernmentAngleReport : Source.AttributedSource
phasedArrayGovernmentAngleReport = Source.mkNoDOISource
  "Mylene Toulgoat; Ross M. Turner"
  "Estimation of target angular position under mainbeam jamming conditions"
  "Defence Research Establishment Ottawa / Government of Canada publication"
  "1995"
  "https://www.publications.gc.ca/site/eng/9.954303/publication.html"
  Source.governmentSource
  "government technical source connecting phased-array multifunction radar, sum/difference beamformers and monopulse angle measurement; citation pays only that bounded technical relationship"
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
  (techIngredientsLead ∷ rfPosePrimary ∷ csiModelSurvey ∷ csiWifiSurvey ∷ spotFiAoAPrimary ∷ wifiCSIAoAToFPrimary ∷ belliniTosiPatentPrimary ∷ belliniTosiNatureHistorical ∷ belliniTosiOxfordArchive ∷ belliniTosiMuseumMechanism ∷ phasedArrayMonopulsePrimary ∷ phasedArrayGovernmentAngleReport ∷ dcsCommunityLead ∷ warThunderCommunityLead ∷ hackadayConsumerWifiLead ∷ hackadaySDRPassiveRadarLead ∷ hackadayPhasedArrayThroughWallLead ∷ [])
  "community leads remain acquisition leads; patent, archival, institutional, government and academic sources pay only bounded source claims; exact observed-hardware provenance, operational use, world-state recovery and authority remain separate"
