module DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmApparatusUncertaintyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionExact as ThreeArm
import DASHI.Wikimedia.IbrahimCannabisTobaccoSharedResidueObservationPanelExact as Panel

------------------------------------------------------------------------
-- PURPOSE
--
-- Close three remaining execution coordinates for the fixed-ratio three-arm
-- cannabis/tobacco experiment:
--   1. exact combustible-carrier geometry;
--   2. analyte-wise residual uncertainty with covariance retained;
--   3. a source-bounded ratio-response escalation design.
--
-- The apparatus below is deliberately a DASHI synthesis of two separate
-- acquisition roots.  No source is promoted to having executed this exact
-- combined geometry+puff protocol.
------------------------------------------------------------------------

record GeometryReceipt : Set where
  constructor geometry-receipt
  field
    sourceLabel : String
    doi : String
    carrierDescription : String
    totalLengthMm : Nat
    tipLengthMm : Nat
    testedFillMassesMg : String
    sourcePuffProtocol : String
    sameAsCanonicalDashiProtocol : Bool
open GeometryReceipt public

eyal2024ConeGeometry : GeometryReceipt
eyal2024ConeGeometry = geometry-receipt
  "Eyal et al. 2024 Inconsistency in the Composition of the Smoke of a Cannabis Cigarette as Smoking Progresses"
  "10.1089/can.2023.0123"
  "commercial conic cannabis-cigarette tube"
  109 40
  "125, 250, or 500 mg ground material"
  "35 mL over 5.6 s, 15 s interval in that source experiment"
  false

record PuffReceipt : Set where
  constructor puff-receipt
  field
    sourceLabel : String
    doi : String
    puffVolumeMl : Nat
    puffDurationSeconds : Nat
    puffIntervalSeconds : Nat
    cannabisAndTobaccoComparedUnderSameRoutine : Bool
    sourceJointGeometryPaid : Bool
open PuffReceipt public

grifiths2020HCIPuff : PuffReceipt
grifiths2020HCIPuff = puff-receipt
  "Comprehensive characterization of mainstream marijuana and tobacco smoke"
  "10.1038/s41598-020-63120-6"
  55 2 30 true false

record CanonicalApparatus : Set where
  constructor canonical-apparatus
  field
    geometrySource : String
    puffSource : String
    totalLengthMm : Nat
    tipLengthMm : Nat
    totalFillMassMg : Nat
    puffVolumeMl : Nat
    puffDurationSeconds : Nat
    puffIntervalSeconds : Nat
    apparatusClass : String
    paperOrTubeIdentity : String
    buttOrStopRule : String
    provenanceMode : String
    copiedWholeFromOneSource : Bool
open CanonicalApparatus public

canonicalThreeArmApparatus : CanonicalApparatus
canonicalThreeArmApparatus = canonical-apparatus
  "Eyal et al. 2024 geometry precedent"
  "Griffiths et al. 2020 HCI comparator precedent"
  109 40 490 55 2 30
  "programmable mainstream-smoking machine with direct downstream particulate collection plus declared gas-phase collection"
  "one fixed commercial cone/tube lot across all arms; material identity recorded"
  "same predeclared stop criterion for C, T and CT; consumed mass recorded and used in normalization"
  "DASHI synthesis: source-bounded geometry combined with independently source-bounded standardized puff routine"
  false

------------------------------------------------------------------------
-- Ratio-response design.
--
-- Hindocha 2017 observed cannabis:tobacco ratios from about 0.05:1 to 1.42:1
-- with a baseline actual mean near 0.53:1.  The three values below are anchors,
-- not quantiles and not claims about population prevalence.
--
-- To avoid confounding ratio with total combustible mass, the ratio-response
-- escalation fixes total plant material at 490 mg, matching the first fixture's
-- total mass and fitting within the 500 mg source-bounded geometry precedent.
------------------------------------------------------------------------

record RatioPoint : Set where
  constructor ratio-point
  field
    label : String
    cannabisToTobaccoRatio : String
    cannabisMassMg : Nat
    tobaccoMassMg : Nat
    totalMassMg : Nat
    sourceRole : String
    populationQuantileClaimed : Bool
open RatioPoint public

lowObservedAnchor : RatioPoint
lowObservedAnchor = ratio-point
  "tobacco-heavy observed-boundary anchor"
  "0.05:1"
  23 467 490
  "derived by fixing 490 mg total mass at the low end of the Hindocha observed ratio range; rounded to whole mg"
  false

centralObservedAnchor : RatioPoint
centralObservedAnchor = ratio-point
  "central source-bounded anchor"
  "0.53:1"
  170 320 490
  "derived by fixing 490 mg total mass near the Hindocha baseline actual mean ratio; rounded to whole mg"
  false

highObservedAnchor : RatioPoint
highObservedAnchor = ratio-point
  "cannabis-heavy observed-boundary anchor"
  "1.42:1"
  288 202 490
  "derived by fixing 490 mg total mass at the high end of the Hindocha observed ratio range; rounded to whole mg"
  false

record RatioSeriesPolicy : Set where
  constructor ratio-series-policy
  field
    totalMassHeldFixed : Bool
    sourceObjectsHeldFixed : Bool
    apparatusHeldFixed : Bool
    puffRoutineHeldFixed : Bool
    ratios : String
    firstQuestion : String
    escalationQuestion : String
    interpolationAuthorityPaid : Bool
open RatioSeriesPolicy public

canonicalRatioSeries : RatioSeriesPolicy
canonicalRatioSeries = ratio-series-policy
  true true true true
  "0.05:1, 0.53:1, 1.42:1 cannabis:tobacco"
  "does R_mix differ from zero at the source-bounded central ratio?"
  "if yes or ambiguous, does sign/magnitude vary across tobacco-heavy to cannabis-heavy source-supported anchors?"
  false

------------------------------------------------------------------------
-- Analyte-wise uncertainty model.
--
-- For analyte j:
--   R_j = Q_CT,j - alpha Q_C,j - beta Q_T,j
--
-- General uncertainty uses the law of propagation of uncertainty.  The simple
-- root-sum-of-squares form is admissible only when covariance terms are zero or
-- demonstrably negligible.  Same-source aliquots and shared calibration can
-- induce correlation, so covariance is retained explicitly by default.
------------------------------------------------------------------------

record ResidualUncertaintyModel : Set where
  constructor residual-uncertainty-model
  field
    measurand : String
    residualEquation : String
    sensitivityCoefficientRule : String
    independentApproximation : String
    covarianceAwareRule : String
    calibrationCovarianceRetained : Bool
    sameSourceCovarianceRetained : Bool
    lowConcentrationSpecialHandling : Bool
    expandedUncertaintyPolicy : String
    sourceBasis : String
open ResidualUncertaintyModel public

canonicalResidualUncertainty : ResidualUncertaintyModel
canonicalResidualUncertainty = residual-uncertainty-model
  "one declared analyte or thermal product in one declared collection phase"
  "R_j = Q_CT,j - alpha*Q_C,j - beta*Q_T,j"
  "derive sensitivities with respect to Q_CT, Q_C, Q_T, alpha and beta; include recovery/calibration terms when not already absorbed into reported Q uncertainty"
  "if inputs are independent: u_c(R_j)^2 = u(Q_CT)^2 + alpha^2 u(Q_C)^2 + beta^2 u(Q_T)^2 plus normalization terms"
  "general rule: add 2*c_i*c_k*cov(x_i,x_k) terms for correlated inputs rather than assuming independence"
  true true true
  "near LOD/LOQ, do not rely blindly on symmetric linear propagation; retain censoring/blank/calibration behaviour and use method-appropriate numerical or Monte Carlo treatment where required"
  "report combined standard uncertainty and, where used, expanded uncertainty with declared coverage factor; threshold decisions must state which quantity they use"
  "Eurachem/CITAC Quantifying Uncertainty in Analytical Measurement: GUM-compatible propagation, covariance handling, low-level caveat, Monte Carlo option"

record InteractionAdmissionRule : Set where
  constructor interaction-admission-rule
  field
    fittingRule : String
    heldOutRule : String
    multiplicityRule : String
    signRule : String
    belowLoqRule : String
    effectMagnitudeRetained : Bool
open InteractionAdmissionRule public

canonicalInteractionAdmission : InteractionAdmissionRule
canonicalInteractionAdmission = interaction-admission-rule
  "predeclare analyte/phase residual and uncertainty model on fitting block; estimate only nuisance parameters allowed by protocol"
  "apply the frozen residual definition and threshold to held-out aliquots from the same homogenized source objects"
  "report analyte-family multiplicity explicitly; exploratory thermal-product discovery is not promoted to confirmatory interaction without a separate validation step"
  "retain positive and negative deviations; non-additivity can increase or decrease transfer"
  "below-LOQ values remain censored/interval-like according to the validated method; zero substitution is not automatic"
  true

------------------------------------------------------------------------
-- The apparatus can support more than one observation path.  Parent analytes,
-- discovered thermal products and aerosol physical properties must not be
-- silently collapsed into a single scalar burden.
------------------------------------------------------------------------

record CollectionArchitecture : Set where
  constructor collection-architecture
  field
    particulateParentLane : String
    gasParentLane : String
    targetedThermalLane : String
    nonTargetThermalLane : String
    aerosolPhysicsLane : String
    crossLaneScalarisationAutomatic : Bool
open CollectionArchitecture public

canonicalCollectionArchitecture : CollectionArchitecture
canonicalCollectionArchitecture = collection-architecture
  "Cambridge/quartz/filter-style particulate collection with matrix-specific recovery/LOQ receipt"
  "declared gas-phase trap/bag method with separate validation; particulate non-detection cannot pay gas absence"
  "predeclared suspected thermal products quantified where standards/methods exist"
  "discovery HRMS/GCxGC lane produces hypotheses that require later identity/quantitation validation"
  "TPM, particle/aerosol mass and puff/burn metadata retained as transfer context"
  false

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data GeometrySourceCreatesPuffProtocol : Set where
data PuffSourceCreatesGeometry : Set where
data SourceRangeCreatesPopulationQuantiles : Set where
data ZeroCovarianceByConvenience : Set where
data BelowLOQCreatesZero : Set where
data DiscoveryFeatureCreatesConfirmedProduct : Set where
data FixedTotalMassCreatesHumanRealism : Set where

geometryDoesNotCreatePuffProtocol : GeometrySourceCreatesPuffProtocol → ⊥
geometryDoesNotCreatePuffProtocol ()

puffDoesNotCreateGeometry : PuffSourceCreatesGeometry → ⊥
puffDoesNotCreateGeometry ()

rangeNotPopulationQuantiles : SourceRangeCreatesPopulationQuantiles → ⊥
rangeNotPopulationQuantiles ()

covarianceNotZeroByConvenience : ZeroCovarianceByConvenience → ⊥
covarianceNotZeroByConvenience ()

belowLoqNotZero : BelowLOQCreatesZero → ⊥
belowLoqNotZero ()

discoveryNotConfirmation : DiscoveryFeatureCreatesConfirmedProduct → ⊥
discoveryNotConfirmation ()

fixedMassNotHumanRealism : FixedTotalMassCreatesHumanRealism → ⊥
fixedMassNotHumanRealism ()

record ApparatusUncertaintyBoundary : Set where
  constructor apparatus-uncertainty-boundary
  field
    exactGeometryPaid : Bool
    exactMachineRoutinePaid : Bool
    exactCombinedSourceProtocolPublished : Bool
    ratioAnchorsPaid : Bool
    ratioAnchorsArePopulationQuantiles : Bool
    covarianceAwareResidualSpecified : Bool
    lowLevelHandlingSpecified : Bool
    actualAnalyteUncertaintyNumbersPaid : Bool
    physicalExecutionPaid : Bool
open ApparatusUncertaintyBoundary public

canonicalApparatusUncertaintyBoundary : ApparatusUncertaintyBoundary
canonicalApparatusUncertaintyBoundary = apparatus-uncertainty-boundary
  true true false true false true true false false
