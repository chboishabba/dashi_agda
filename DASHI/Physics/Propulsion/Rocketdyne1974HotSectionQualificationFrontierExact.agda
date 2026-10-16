{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974HotSectionQualificationFrontierExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.QualifiedHotSectionManufacturingBidiExact as Hot

------------------------------------------------------------------------
-- CANONICAL QUALIFICATION REVERSE-PAYMENT WELD
------------------------------------------------------------------------

processRouteObligation : Hot.QualificationReverseObligation
processRouteObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireProcessRouteAndRevision
    "1974 WC103/VH-101 fabrication traveler, surface-treatment, coating/braze process record and revision identity"
    "same-object process-history coordinate for qualification"
    "cannot promote material identity or one successful firing into a qualified manufactured article"

thermalHistoryObligation : Hot.QualificationReverseObligation
thermalHistoryObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireThermalOrProcessHistory
    "complete Test-052/Test-768/Test-870-2 temperature and heat-flux histories, Test-052 model/referent numerical comparison and uncertainty, plus article thermal-processing history"
    "bounded same-object thermal-history and model-credibility payment"
    "cannot manufacture a creep lifetime, off-design predictive model or temperature-dependent failure law from peak temperature/source-reported graphical agreement alone"

geometryRevisionObligation : Hot.QualificationReverseObligation
geometryRevisionObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireGeometryOrPatternRevision
    "local nozzle wall gauge, contour, joint/support geometry and exact article revision"
    "same-object stress geometry"
    "cannot infer unique applied stress from pressure and temperature without geometry"

inspectionObligation : Hot.QualificationReverseObligation
inspectionObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireInspectionAndMetrology
    "1974 pre/post-test NDE and dimensional/coating inspection bound to the exact nozzle article/revision, including method, coverage, defect class, sensitivity/POD basis, acceptance threshold and chronology where quantitative detection credit is claimed"
    "same-object inspection-capability receipt"
    "inspection mention alone does not establish quantitative flaw-detection capability; later NASA POD requirements and later Shuttle C-103 NDE history do not transfer retroactively"

defectAcceptanceObligation : Hot.QualificationReverseObligation
defectAcceptanceObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireDefectAcceptanceCriteria
    "1974 allowable flaw/coating/braze acceptance criteria and disposition limits"
    "defect-acceptance coordinate"
    "cannot infer acceptance criteria from absence of a reported incident"

operatingEnvelopeObligation : Hot.QualificationReverseObligation
operatingEnvelopeObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireOperatingEnvelope
    "approved pressure/mixture-ratio/thermal/environmental envelope tied to the exact material/process revision"
    "bounded operating-envelope payment"
    "off-limits demonstrations do not imply unlimited admissible operation"

lifeReliabilityObligation : Hot.QualificationReverseObligation
lifeReliabilityObligation =
  Hot.qualification-reverse-obligation
    Hot.acquireLifeReliabilityEvidence
    "population/lot or repeated-article evidence supporting reuse/lifetime after the WC103 revision"
    "lifetime/reliability payment"
    "one 45-second successful follow-up cannot establish fatigue/creep life, 100-mission life or 100000-second life"

record RocketdyneQualificationReverseFrontier : Set where
  constructor rocketdyne-qualification-reverse-frontier
  field
    processRoute : Hot.QualificationReverseObligation
    thermalHistory : Hot.QualificationReverseObligation
    geometryRevision : Hot.QualificationReverseObligation
    inspection : Hot.QualificationReverseObligation
    defectAcceptance : Hot.QualificationReverseObligation
    operatingEnvelope : Hot.QualificationReverseObligation
    lifeReliability : Hot.QualificationReverseObligation
    engineTestEvidenceAlreadyExists : Bool
    sameObjectQualificationCarrierComplete : Bool
    currentQualificationStatus : String

rocketdyneQualificationReverseFrontier : RocketdyneQualificationReverseFrontier
rocketdyneQualificationReverseFrontier =
  rocketdyne-qualification-reverse-frontier
    processRouteObligation
    thermalHistoryObligation
    geometryRevisionObligation
    inspectionObligation
    defectAcceptanceObligation
    operatingEnvelopeObligation
    lifeReliabilityObligation
    true false
    "engine-test and bounded material/environment observations exist, but the canonical same-object process + quantitative inspection capability + validated model/envelope + lifetime qualification payment remains incomplete"

fullQualificationPaymentStillOpen : Bool
fullQualificationPaymentStillOpen = true

canonicalHotSectionQualificationBoundary : Hot.CanonicalQualificationBoundary
canonicalHotSectionQualificationBoundary = Hot.canonicalQualificationBoundary
