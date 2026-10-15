module DASHI.Chemistry.LineageAttributionEvidencePaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact as Atlas
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4
import DASHI.Biology.IonicMimicrySourceAtlasExact as Ionic

------------------------------------------------------------------------
-- SOURCE-COORDINATE PAYMENT
--
-- Citation and proof are deliberately separate.  Each receipt says which
-- coordinate the source pays, what role the source plays, and what remains
-- unpaid.  DASHI composition/synthesis is never retroactively attributed to an
-- external source merely because the source supplies an input coordinate.
------------------------------------------------------------------------

data EvidenceRole : Set where
  primaryExperiment : EvidenceRole
  primaryStructuralStudy : EvidenceRole
  curatedReactionDatabase : EvidenceRole
  technicalReference : EvidenceRole
  reviewSynthesis : EvidenceRole
  backgroundPrimer : EvidenceRole

data PaymentGrade : Set where
  identityPaid : PaymentGrade
  qualitativeMechanismPaid : PaymentGrade
  sourceConditionedEmpiricalPaid : PaymentGrade
  quantitativeCalibrationPaid : PaymentGrade
  unpaid : PaymentGrade

record SourceCoordinatePayment : Set where
  constructor sourceCoordinatePayment
  field
    source : Source.AttributedSource
    role : EvidenceRole
    coordinateKey : String
    exactLocatorReference : String
    sourceBoundedClaim : String
    dashiConsumerReference : String
    grade : PaymentGrade
    unpaidResidual : String
    sourceOwnsDASHISynthesis : Bool
    sourceOwnsDASHISynthesisIsFalse : sourceOwnsDASHISynthesis ≡ false
    citationCreatesProof : Bool
    citationCreatesProofIsFalse : citationCreatesProof ≡ false

open SourceCoordinatePayment public

chlorAlkaliTechnicalPayment : SourceCoordinatePayment
chlorAlkaliTechnicalPayment =
  sourceCoordinatePayment
    Atlas.chlorAlkaliBREF2014
    technicalReference
    "gold-R1 industrial brine-electrolysis/process identity"
    "JRC91156 / EUR 26844 EN; chlor-alkali production scope and brine electrolysis process description"
    "Production of chlorine, hydrogen and caustic products by electrolysis of brine is within the source's technical scope."
    "GoldReactionReplaySuiteExact.chlorAlkaliReplay + canonical half-reaction owner"
    identityPaid
    "electrode-specific potentials, materials, current density, rate constants, interfacial geometry and microscopic mechanism"
    false refl false refl

pahMechanismPayment : SourceCoordinatePayment
pahMechanismPayment =
  sourceCoordinatePayment
    BH4.aromaticHydroxylaseReview
    reviewSynthesis
    "gold-R2 BH4/O2/non-heme-iron aromatic hydroxylase mechanism family"
    "Roberts/Fitzpatrick 2013 review; DOI 10.1002/iub.1144"
    "Review-level support for BH4/oxygen/iron-dependent aromatic amino-acid hydroxylation mechanism family."
    "GoldReactionReplaySuiteExact.pahReplay"
    qualitativeMechanismPaid
    "PAH-specific atom map, exact intermediate trajectory, assay-specific Km/Vmax, compartment concentration and measured in-vivo flux"
    false refl false refl

sprReactionPayment : SourceCoordinatePayment
sprReactionPayment =
  sourceCoordinatePayment
    BH4.bRENDAspr
    curatedReactionDatabase
    "gold-R3 SPR BH4-forming reaction identity"
    "BRENDA EC 1.1.1.153"
    "Curated enzyme/reaction identity for sepiapterin reductase and NADPH-dependent BH4-forming reduction."
    "KitzerowBH4SynthesisRegenerationExact.sprReaction"
    identityPaid
    "organism/isoform-specific kinetics, concentrations, exact atom/electron-density map and in-vivo branch flux"
    false refl false refl

pbCaStructuralPayment : SourceCoordinatePayment
pbCaStructuralPayment =
  sourceCoordinatePayment
    Ionic.kirbergerYang2008
    primaryStructuralStudy
    "gold-R4 Pb/Ca coordination-site structural separation"
    "DOI 10.1016/j.jinorgbio.2008.06.014"
    "Source-bounded comparison of Pb2+ and Ca2+ protein coordination sites, including shared donor chemistry and differing coordination characteristics."
    "LeadCalciumEndToEndReplayExact + AtomicLineageTargetRecognitionBridgeExact"
    sourceConditionedEmpiricalPaid
    "universal protein substitution, organism dose-response, all-site affinity ordering and downstream phenotype"
    false refl false refl

pbCaFunctionalPayment : SourceCoordinatePayment
pbCaFunctionalPayment =
  sourceCoordinatePayment
    Ionic.habermannEtAl1983
    primaryExperiment
    "gold-R4 calmodulin functional substitution"
    "DOI 10.1007/BF00277816"
    "Pb2+ can substitute for Ca2+ in several source-assayed calmodulin-dependent contexts."
    "LeadCalciumEndToEndReplayExact"
    sourceConditionedEmpiricalPaid
    "all calcium-binding targets, same downstream action, population toxicity or clinical inference"
    false refl false refl

carbonContextPayment : SourceCoordinatePayment
carbonContextPayment =
  sourceCoordinatePayment
    Atlas.astrobiologyPrimer2016
    backgroundPrimer
    "gold-R5 carbon-rich terrestrial biochemistry / origins context"
    "Astrobiology 16(8):561-653; DOI 10.1089/ast.2015.1460"
    "Broad astrobiology review context for carbon-rich known biochemistry and origin-of-life research."
    "CarbonSiliconReachableChemistryBenchmarkExact"
    qualitativeMechanismPaid
    "matched carbon/silicon reaction-cone experiment, unique-life-substrate claim, abiogenesis and life inevitability"
    false refl false refl

canonicalSourceCoordinatePayments : List SourceCoordinatePayment
canonicalSourceCoordinatePayments =
  chlorAlkaliTechnicalPayment
  ∷ pahMechanismPayment
  ∷ sprReactionPayment
  ∷ pbCaStructuralPayment
  ∷ pbCaFunctionalPayment
  ∷ carbonContextPayment
  ∷ []

record LineageAttributionBoundary : Set where
  constructor lineageAttributionBoundary
  field
    externalResultEqualsDASHISynthesis : Bool
    externalResultEqualsDASHISynthesisIsFalse : externalResultEqualsDASHISynthesis ≡ false
    dashiCompositionTransfersToSource : Bool
    dashiCompositionTransfersToSourceIsFalse : dashiCompositionTransfersToSource ≡ false
    citationAlonePaysCalibration : Bool
    citationAlonePaysCalibrationIsFalse : citationAlonePaysCalibration ≡ false
    sourceRoleCollapsed : Bool
    sourceRoleCollapsedIsFalse : sourceRoleCollapsed ≡ false
    missingCoordinatePromotedByNearbyCitation : Bool
    missingCoordinatePromotedByNearbyCitationIsFalse : missingCoordinatePromotedByNearbyCitation ≡ false
    reviewCountsAsPrimaryExperimentByDefault : Bool
    reviewCountsAsPrimaryExperimentByDefaultIsFalse : reviewCountsAsPrimaryExperimentByDefault ≡ false
    databaseReactionIdentityCountsAsInVivoFlux : Bool
    databaseReactionIdentityCountsAsInVivoFluxIsFalse : databaseReactionIdentityCountsAsInVivoFlux ≡ false
    sourcePriorityCreatedByDASHIReuse : Bool
    sourcePriorityCreatedByDASHIReuseIsFalse : sourcePriorityCreatedByDASHIReuse ≡ false
    exactLocatorRequiredForNumericPromotion : Bool
    exactLocatorRequiredForNumericPromotionIsTrue : exactLocatorRequiredForNumericPromotion ≡ true
    reading : String

open LineageAttributionBoundary public

canonicalLineageAttributionBoundary : LineageAttributionBoundary
canonicalLineageAttributionBoundary =
  lineageAttributionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "External sources retain authorship and authority only for source-bounded coordinates. DASHI owns its formal composition, adapters, cross-source inferences and non-promotion theorems. Citation never creates proof, priority, calibration or authority; numeric promotion requires an exact source locator and matching measurement context."
