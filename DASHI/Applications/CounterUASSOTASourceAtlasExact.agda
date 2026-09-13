module DASHI.Applications.CounterUASSOTASourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- COUNTER-UAS SOTA SOURCE ATLAS
--
-- Academic references are retained as attributed sources.  They pay bounded
-- architecture/evaluation coordinates; citation does not import proof,
-- validate any specific vendor, or create operational/legal authority.
------------------------------------------------------------------------

harmelEtAl2026 : Source.AttributedSource
harmelEtAl2026 =
  Source.mkDOISource
    "François Harmel; Alexandre Heuchamps; Alexandre Papy; Marijke Vandewal"
    "Towards a Standardised Framework for Evaluating Sensor Performance in C-sUAS Systems"
    "Drones 10(7), 517"
    "2026"
    "10.3390/drones10070517"
    "https://doi.org/10.3390/drones10070517"
    Source.academicArticleSource
    "source for defensive C-sUAS sensor-performance modelling across EO, thermal IR, acoustic, RF, radar and lidar, with explicit target/environment/sensor assumptions and boundary conditions; it does not address effector design"
    Source.publicAttribution

johnsonMoorePorter2026 : Source.AttributedSource
johnsonMoorePorter2026 =
  Source.mkDOISource
    "Stephanie L. Johnson; Hunter D. Moore; Michael D. Porter"
    "Toward resilient multi-modal drone detection in cluttered environments: A systems survey of EO/IR, radar, acoustic, LiDAR and RF modalities"
    "International Journal of Critical Infrastructure Protection 54, 100870"
    "2026"
    "10.1016/j.ijcip.2026.100870"
    "https://doi.org/10.1016/j.ijcip.2026.100870"
    Source.academicArticleSource
    "source for the modality-complementarity and degraded-environment boundary: no unimodal sensor is reliable across all cluttered/NLOS settings, and fusion must be evaluated with degradation as a design assumption"
    Source.publicAttribution

changRazHiebGanesan2026 : Source.AttributedSource
changRazHiebGanesan2026 =
  Source.mkDOISource
    "Kuochu C. Chang; Ali Raz; Michael R. Hieb; Rajesh Ganesan"
    "From ROC to SOC: A Predictive Sensor Fusion Framework for Counter Uncrewed Aerial Vehicles"
    "IEEE Transactions on Aerospace and Electronic Systems"
    "2026"
    "10.1109/TAES.2026.3666835"
    "https://doi.org/10.1109/TAES.2026.3666835"
    Source.academicArticleSource
    "source for treating multi-sensor fusion as a system-level detection/false-alarm trade-off rather than inferring fused performance from isolated sensor ROC claims"
    Source.publicAttribution

deCubberEtAl2025 : Source.AttributedSource
deCubberEtAl2025 =
  Source.mkDOISource
    "Geert De Cubber et al."
    "Standardized Evaluation of Counter-Drone Systems: Methods, Technologies, and Performance Metrics"
    "Drones 9(5), 354"
    "2025"
    "10.3390/drones9050354"
    "https://doi.org/10.3390/drones9050354"
    Source.academicArticleSource
    "source for scenario-based quantitative and qualitative evaluation of counter-drone detection, tracking and identification systems; evaluation methodology does not itself create deployment authority"
    Source.publicAttribution

semenyukEtAl2025 : Source.AttributedSource
semenyukEtAl2025 =
  Source.mkDOISource
    "Vladislav Semenyuk; Ildar Kurmashev; Alberto Lupidi; Dmitriy Alyoshin; Liliya Kurmasheva; Alessandro Cantelli-Forti"
    "Advances in UAV detection: integrating multi-sensor systems and AI for enhanced accuracy and efficiency"
    "International Journal of Critical Infrastructure Protection 49, 100744"
    "2025"
    "10.1016/j.ijcip.2025.100744"
    "https://doi.org/10.1016/j.ijcip.2025.100744"
    Source.academicArticleSource
    "review source for radar, RF, optical and acoustic UAV detection plus multi-sensor fusion and AI/ML integration; broad review evidence is not product-specific validation"
    Source.publicAttribution

seidaliyevaEtAl2024 : Source.AttributedSource
seidaliyevaEtAl2024 =
  Source.mkDOISource
    "Ulzhalgas Seidaliyeva; Lyazzat Ilipbayeva; Kyrmyzy Taissariyeva; Nurzhigit Smailov; Eric T. Matson"
    "Advances and Challenges in Drone Detection and Classification Techniques: A State-of-the-Art Review"
    "Sensors 24(1), 125"
    "2024"
    "10.3390/s24010125"
    "https://doi.org/10.3390/s24010125"
    Source.academicArticleSource
    "state-of-the-art review source for radar, RF, acoustic and vision detection/classification modalities, their distinct limitations, and the role of fusion"
    Source.publicAttribution

counterUASSOTASources : List Source.AttributedSource
counterUASSOTASources =
  harmelEtAl2026 ∷
  johnsonMoorePorter2026 ∷
  changRazHiebGanesan2026 ∷
  deCubberEtAl2025 ∷
  semenyukEtAl2025 ∷
  seidaliyevaEtAl2024 ∷
  []

counterUASSOTASourceAtlas : Source.AttributedSourceAtlas
counterUASSOTASourceAtlas =
  Source.mkSourceAtlas
    "counter-UAS sensing and fusion SOTA"
    "DASHI.Applications.CounterUASSOTASourceAtlasExact"
    counterUASSOTASources
    "bounded source atlas for defensive sensing modalities, multi-sensor fusion, degraded-condition evaluation, scenario assumptions, detection/false-alarm trade-offs, and test methodology; excludes offensive UAS design and does not confer mitigation authority"

counterUASSOTASourceAtlasCreatesAuthority : Bool
counterUASSOTASourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority counterUASSOTASourceAtlas

counterUASSOTASourceAtlasCreatesAuthorityIsFalse :
  counterUASSOTASourceAtlasCreatesAuthority ≡ false
counterUASSOTASourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse counterUASSOTASourceAtlas

record CounterUASSOTASourceBoundary : Set where
  constructor counterUASSOTASourceBoundary
  field
    academicReviewIsProductSpecificValidation : Bool
    academicReviewIsProductSpecificValidationIsFalse :
      academicReviewIsProductSpecificValidation ≡ false
    manufacturerSpecificationIsStandardisedFieldPerformance : Bool
    manufacturerSpecificationIsStandardisedFieldPerformanceIsFalse :
      manufacturerSpecificationIsStandardisedFieldPerformance ≡ false
    sensingEvidenceCreatesMitigationAuthority : Bool
    sensingEvidenceCreatesMitigationAuthorityIsFalse :
      sensingEvidenceCreatesMitigationAuthority ≡ false

canonicalCounterUASSOTASourceBoundary : CounterUASSOTASourceBoundary
canonicalCounterUASSOTASourceBoundary =
  counterUASSOTASourceBoundary false refl false refl false refl
