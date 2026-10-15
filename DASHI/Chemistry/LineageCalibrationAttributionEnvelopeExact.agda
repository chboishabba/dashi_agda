module DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Chemistry.GoldReactionReplaySuiteExact as Gold
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4Sources
import DASHI.Biology.IonicMimicrySourceAtlasExact as IonicSources

------------------------------------------------------------------------
-- ATTRIBUTION ENVELOPES FOR LINEAGE / CALIBRATION REPLAYS
--
-- External sources own the empirical/source facts explicitly attributed to
-- them. DASHI owns the cross-source composition, lineage hyperfabric,
-- discriminator synthesis, formal non-promotion boundaries and any theorem
-- proved by those constructions. Citation never transfers ownership of DASHI
-- synthesis to the cited source, nor imports proof or numeric calibration.
------------------------------------------------------------------------

chlorAlkaliEuroChlor2022 : Source.AttributedSource
chlorAlkaliEuroChlor2022 =
  Source.mkNoDOISource
    "Euro Chlor / Cefic"
    "Eco-profile and Environmental Product Declaration: Chlorine (The Chlor-Alkali Process)"
    "Euro Chlor eco-profile"
    "2022"
    "https://www.eurochlor.org/wp-content/uploads/2022/09/Eco_profile-study-update-September-2022.pdf"
    Source.institutionalSource
    "source for standard industrial chlor-alkali process and electrode-reaction context; does not pay DASHI atom lineage, microkinetics or interfacial electron density"
    Source.publicAttribution

dhprBrenda2026 : Source.AttributedSource
dhprBrenda2026 =
  Source.mkNoDOISource
    "BRENDA Enzyme Database"
    "EC 1.5.1.34 6,7-dihydropteridine reductase"
    "BRENDA release 2026.1"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=1.5.1.34"
    Source.institutionalSource
    "reaction-identity source for DHPR-mediated pterin reduction; does not pay assay-specific kinetics, flux allocation or autism causation"
    Source.publicAttribution

astrobiologyPrimer2016 : Source.AttributedSource
astrobiologyPrimer2016 =
  Source.mkDOISource
    "Shawn D. Domagal-Goldman; Katherine E. Wright; et al."
    "The Astrobiology Primer v2.0"
    "Astrobiology 16(8):561-653"
    "2016"
    "10.1089/ast.2015.1460"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC5008114/"
    Source.academicArticleSource
    "broad source for carbon-rich terrestrial biochemistry and staged prebiotic-chemistry context; does not prove carbon uniqueness, abiogenesis or DASHI reachable-chemistry constructions"
    Source.publicAttribution

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
    chlorAlkaliEuroChlor2022
    (Snowball.canonicalSourceRoleSnowballReceipt chlorAlkaliEuroChlor2022)
    "process description / electrode-reaction section"
    "standard chloride electrolysis and co-product process context"
    "DASHI composes existing transition owners with typed lineage/electron/bond audit"
    mixedPaidUnpaid
    "exact plant conditions, potentials, current density, microkinetics and interfacial structure"
    "public Euro Chlor report; exact page/figure locator remains acquisition coordinate where needed"
    false refl false refl

pahEnvelope : ReplayAttributionEnvelope
pahEnvelope =
  replayAttributionEnvelope
    Gold.pahReplay
    pahMechanismSource
    (Snowball.canonicalSourceRoleSnowballReceipt pahMechanismSource)
    "aromatic amino-acid hydroxylase mechanism review"
    "BH4/O2/non-heme-iron hydroxylation mechanism family"
    "DASHI instantiates PAH as a lineage replay and keeps atom-map/kinetic residuals explicit"
    mixedPaidUnpaid
    "site-specific isotope map, catalytic intermediates and assay kinetics"
    "PMCID/DOI article manifestation identified; replay-specific exact locator remains separable"
    false refl false refl

dhprEnvelope : ReplayAttributionEnvelope
dhprEnvelope =
  replayAttributionEnvelope
    Gold.dhprReplay
    dhprBrenda2026
    (Snowball.canonicalSourceRoleSnowballReceipt dhprBrenda2026)
    "EC 1.5.1.34 reaction identity"
    "DHPR pterin reduction identity"
    "DASHI retains NADH electron-equivalent lineage and flux-model boundary"
    mixedPaidUnpaid
    "exact isotope map, redox potential and assay-specific kinetic constants"
    "BRENDA enzyme record; numeric assay manifestation must be separately located"
    false refl false refl

pbCaEnvelope : ReplayAttributionEnvelope
pbCaEnvelope =
  replayAttributionEnvelope
    Gold.pbCaReplay
    pbCaGeometrySource
    (Snowball.canonicalSourceRoleSnowballReceipt pbCaGeometrySource)
    "protein Pb2+/Ca2+ coordination-site structural comparison"
    "shared donor usage plus distinct coordination-number/geometry evidence"
    "DASHI generalises the source-bounded comparison into a target-relative lineage discriminator"
    mixedPaidUnpaid
    "target-specific affinity, occupancy, kinetics and whole-organism dose-response"
    "DOI article identified; individual structural observations retain source-specific context"
    false refl false refl

carbonEnvelope : ReplayAttributionEnvelope
carbonEnvelope =
  replayAttributionEnvelope
    Gold.carbonBondReplay
    astrobiologyPrimer2016
    (Snowball.canonicalSourceRoleSnowballReceipt astrobiologyPrimer2016)
    "prebiotic chemistry stages / carbon-rich terrestrial biochemistry context"
    "broad environmental and prebiotic context"
    "DASHI owns carbon-vs-alternative reachable-chemistry benchmark and BIDI discriminator"
    sourceIdentityOnly
    "specific reaction identity, atom map, yield, kinetics, competing products and matched silicon comparison"
    "PMCID/DOI article manifestation identified; no specific reaction is promoted from the overview"
    false refl false refl

canonicalReplayAttributionEnvelopes : List ReplayAttributionEnvelope
canonicalReplayAttributionEnvelopes =
  chlorEnvelope ∷ pahEnvelope ∷ dhprEnvelope ∷ pbCaEnvelope ∷ carbonEnvelope ∷ []

record LineageCalibrationAttributionBoundary : Set where
  constructor lineageCalibrationAttributionBoundary
  field
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
    true refl true refl true refl false refl false refl false refl false refl
