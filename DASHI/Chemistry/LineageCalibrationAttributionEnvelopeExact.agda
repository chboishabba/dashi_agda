module DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Chemistry.GoldReactionReplaySuiteExact as Gold
import DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact as Atlas
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4Sources
import DASHI.Biology.IonicMimicrySourceAtlasExact as IonicSources

------------------------------------------------------------------------
-- ATTRIBUTION ENVELOPES FOR LINEAGE / CALIBRATION REPLAYS
-- Canonical source identities come from their source-atlas owners; this module
-- attaches those identities to DASHI replay consumers without re-authoring them.
------------------------------------------------------------------------

chlorAlkaliTechnicalSource : Source.AttributedSource
chlorAlkaliTechnicalSource = Atlas.chlorAlkaliEuroChlor2022

astrobiologyPrimerSource : Source.AttributedSource
astrobiologyPrimerSource = Atlas.astrobiologyPrimer2016

dhprBrenda2026 : Source.AttributedSource
dhprBrenda2026 = Atlas.dhprBRENDA2026

pahMechanismSource : Source.AttributedSource
pahMechanismSource = BH4Sources.aromaticHydroxylaseReview

pbCaGeometrySource : Source.AttributedSource
pbCaGeometrySource = IonicSources.kirbergerYang2008

data PaymentState : Set where
  sourceIdentityOnly : PaymentState
  qualitativeCoordinatePaid : PaymentState
  quantitativeCoordinatePaid : PaymentState
  mixedPaidUnpaid : PaymentState

record ReplayAttributionEnvelope : Set₁ where
  constructor replayAttributionEnvelope
  field
    replay : Gold.GoldReactionReplay
    source : Source.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    sourceLocator : String
    sourceClaimRole : String
    dashiFormalisationRole : String
    paymentState : PaymentState
    unpaidResidual : String
    sameObjectManifestationReference : String
    sourceOwnsDashiComposition : Bool
    sourceOwnsDashiCompositionIsFalse : sourceOwnsDashiComposition ≡ false
    citationCreatesNumericPayment : Bool
    citationCreatesNumericPaymentIsFalse : citationCreatesNumericPayment ≡ false

open ReplayAttributionEnvelope public

chlorEnvelope : ReplayAttributionEnvelope
chlorEnvelope =
  replayAttributionEnvelope
    Gold.chlorAlkaliReplay
    chlorAlkaliTechnicalSource
    (Snowball.canonicalSourceRoleSnowballReceipt chlorAlkaliTechnicalSource)
    "Euro Chlor September-2022 final-report update; process/product description level only"
    "European chlor-alkali electrolysis/product context"
    "DASHI composes existing transition owners with typed lineage/electron/bond audit"
    mixedPaidUnpaid
    "exact half-reaction source locator, plant conditions, electrode potentials/current density, microkinetics and interfacial structure"
    "canonical Euro Chlor source object reused; exact numeric manifestation remains an acquisition coordinate"
    false refl false refl

pahEnvelope : ReplayAttributionEnvelope
pahEnvelope =
  replayAttributionEnvelope
    Gold.pahReplay
    pahMechanismSource
    (Snowball.canonicalSourceRoleSnowballReceipt pahMechanismSource)
    "aromatic amino-acid hydroxylase mechanism review; DOI 10.1002/iub.1144"
    "BH4/O2/non-heme-iron hydroxylation mechanism family"
    "DASHI instantiates PAH as a lineage replay and keeps atom-map/kinetic residuals explicit"
    mixedPaidUnpaid
    "PAH-specific isotope map, catalytic intermediates and assay kinetics"
    "DOI/PMCID manifestation identified; replay-specific exact locator remains separately payable"
    false refl false refl

dhprEnvelope : ReplayAttributionEnvelope
dhprEnvelope =
  replayAttributionEnvelope
    Gold.dhprReplay
    dhprBrenda2026
    (Snowball.canonicalSourceRoleSnowballReceipt dhprBrenda2026)
    "BRENDA/IUBMB EC 1.5.1.34 reaction identity"
    "DHPR pterin redox reaction identity"
    "DASHI retains NADH electron-equivalent lineage and flux-model boundary"
    mixedPaidUnpaid
    "exact quinonoid-species instantiation, isotope map, redox potential, assay-specific kinetics and in-vivo flux"
    "canonical BRENDA source object reused; numeric primary-assay manifestation must be separately located"
    false refl false refl

pbCaEnvelope : ReplayAttributionEnvelope
pbCaEnvelope =
  replayAttributionEnvelope
    Gold.pbCaReplay
    pbCaGeometrySource
    (Snowball.canonicalSourceRoleSnowballReceipt pbCaGeometrySource)
    "Kirberger/Yang 2008; DOI 10.1016/j.jinorgbio.2008.06.014"
    "source-conditioned Pb2+/Ca2+ protein coordination-site comparison"
    "DASHI generalises the source-bounded comparison into a target-relative lineage discriminator"
    mixedPaidUnpaid
    "same-target affinity, occupancy, kinetics, functional coupling and whole-organism dose-response"
    "DOI article identified; individual structural observations retain source-specific context"
    false refl false refl

carbonEnvelope : ReplayAttributionEnvelope
carbonEnvelope =
  replayAttributionEnvelope
    Gold.carbonBondReplay
    astrobiologyPrimerSource
    (Snowball.canonicalSourceRoleSnowballReceipt astrobiologyPrimerSource)
    "Astrobiology 16(8):561-653; DOI 10.1089/ast.2015.1460"
    "broad carbon-rich terrestrial biochemistry and prebiotic-context review"
    "DASHI owns carbon-vs-alternative reachable-chemistry benchmark and BIDI discriminator"
    sourceIdentityOnly
    "specific reaction identity, atom map, yield, kinetics, competing products and matched silicon comparison"
    "canonical Astrobiology Primer source reused; no specific reaction is promoted from the overview"
    false refl false refl

canonicalReplayAttributionEnvelopes : List ReplayAttributionEnvelope
canonicalReplayAttributionEnvelopes =
  chlorEnvelope ∷ pahEnvelope ∷ dhprEnvelope ∷ pbCaEnvelope ∷ carbonEnvelope ∷ []

record LineageCalibrationAttributionBoundary : Set where
  constructor lineageCalibrationAttributionBoundary
  field
    canonicalSourceAtlasReusedWhereAvailable : Bool
    canonicalSourceAtlasReusedWhereAvailableIsTrue : canonicalSourceAtlasReusedWhereAvailable ≡ true
    everyReplayCarriesAttributedSource : Bool
    everyReplayCarriesAttributedSourceIsTrue : everyReplayCarriesAttributedSource ≡ true
    sourceRoleSnowballs : Bool
    sourceRoleSnowballsIsTrue : sourceRoleSnowballs ≡ true
    unpaidCoordinateRetainsSource : Bool
    unpaidCoordinateRetainsSourceIsTrue : unpaidCoordinateRetainsSource ≡ true
    citationCreatesNumericPayment : Bool
    citationCreatesNumericPaymentIsFalse : citationCreatesNumericPayment ≡ false
    citationCreatesScientificAuthority : Bool
    citationCreatesScientificAuthorityIsFalse : citationCreatesScientificAuthority ≡ false
    dashiSynthesisAttributedToExternalSource : Bool
    dashiSynthesisAttributedToExternalSourceIsFalse : dashiSynthesisAttributedToExternalSource ≡ false
    sourceObservationAttributedToDashi : Bool
    sourceObservationAttributedToDashiIsFalse : sourceObservationAttributedToDashi ≡ false

open LineageCalibrationAttributionBoundary public

canonicalLineageCalibrationAttributionBoundary : LineageCalibrationAttributionBoundary
canonicalLineageCalibrationAttributionBoundary =
  lineageCalibrationAttributionBoundary
    true refl true refl true refl true refl false refl false refl false refl false refl
