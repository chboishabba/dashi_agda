module DASHI.Law.SensibLawWoogarooIbrahimS102S13SotaExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooIbrahimPopulationSourceExtensionExact as Population
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN IBRAHIM/SNOWBALL EXTENSION FOR LIVE s 102 / s 13 CONSUMERS
--
-- Adds only sources that sharpen an already-open legal/ecological consumer.
-- DOI, QID and Dewey are navigation/provenance coordinates.  They do not
-- manufacture scientific truth, same-object identity or a legal conclusion.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryEmpiricalArticle : SourceRole
  primaryGovernmentPracticeRecord : SourceRole
  primaryStatutorySource : SourceRole
  crossProjectEmpiricalAudit : SourceRole

data LocalityClass : Set where
  sameObjectSpringview : LocalityClass
  southEastQueenslandRegional : LocalityClass
  australianNationalComparator : LocalityClass
  generalStatutoryPractice : LocalityClass

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

habitatFragmentationQid : Id.ItemId
habitatFragmentationQid = Id.itemId "Q913302"

wildlifeCorridorQid : Id.ItemId
wildlifeCorridorQid = Id.itemId "Q864912"

environmentalLawQid : Id.ItemId
environmentalLawQid = Id.itemId "Q328798"

endangeredSpeciesQid : Id.ItemId
endangeredSpeciesQid = Id.itemId "Q11394"

koalaDewey ecologyDewey conservationDewey lawDewey : String
koalaDewey = "599.25"
ecologyDewey = "577"
conservationDewey = "333.95"
lawDewey = "340.000"

------------------------------------------------------------------------
-- Newly added attributed sources.
------------------------------------------------------------------------

rus2021 : Source.AttributedSource
rus2021 = Source.mkDOISource
  "Adrian I. Rus; Clare McArthur; Valentina S. A. Mella; Mathew S. Crowther"
  "Habitat fragmentation affects movement and space use of a specialist folivore, the koala"
  "Animal Conservation 24, 26-37"
  "2021"
  "10.1111/acv.12596"
  "https://doi.org/10.1111/acv.12596"
  Source.academicArticleSource
  "Primary GPS-tracking study. Decreasing functional connectivity was associated with longer and more direct koala movements and use of more core patches. Used as general movement/fragmentation mechanism evidence only; the study landscape is not Springview/Woogaroo."
  Source.publicAttribution

dexter2018 : Source.AttributedSource
dexter2018 = Source.mkDOISource
  "Cathryn E. Dexter; Robert G. Appleby; J. Scott; Jason P. Edgar; Darryl N. Jones"
  "Individuals matter: predicting koala road crossing behaviour in south-east Queensland"
  "Australian Mammalogy 40(1), 67-75"
  "2018"
  "10.1071/AM16043"
  "https://doi.org/10.1071/AM16043"
  Source.academicArticleSource
  "Primary South East Queensland road-crossing study of six koala subpopulations. It supports individual- and proximity-dependent road-risk questions, not a Springview crossing rate or population estimate."
  Source.publicAttribution

tranMaron2024 : Source.AttributedSource
tranMaron2024 = Source.mkDOISource
  "Hao Nguyen Tran; Martine Maron"
  "Biodiversity offset conditions contributing to net loss of koala Phascolarctos cinereus habitat"
  "Conservation Science and Practice 6(12), e13271"
  "2024"
  "10.1111/csp2.13271"
  "https://doi.org/10.1111/csp2.13271"
  Source.academicArticleSource
  "Cross-project empirical audit of all EPBC-permitted koala habitat development impacts identified for 2012-2021 (n=98). Used to identify known offset-accounting failure modes such as optimistic averted-loss assumptions and double counting; it does not determine the adequacy of the 2019/8575 offsets."
  Source.publicAttribution

nca105Current : Source.AttributedSource
nca105Current = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — section 105 Duration of order"
  "Queensland Legislation, current in-force Act"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary statutory source: an interim conservation order has effect for not more than 60 days and may be extended by Governor in Council gazette notice by not more than 90 days. Used for remedy-duration strategy, not merits proof."
  Source.publicAttribution

nightParrotAdministration2016 : Source.AttributedSource
nightParrotAdministration2016 = Source.mkNoDOISource
  "Queensland Government / Department administering the Nature Conservation Act 1992"
  "Report on the administration of the Nature Conservation Act 1992, 1 July 2015 to 30 June 2016"
  "Queensland Parliament tabled annual administration report"
  "2016"
  "https://www.parliament.qld.gov.au/Work-of-the-Assembly/Tabled-Papers/docs/5516T2248/5516t2248.pdf"
  Source.governmentSource
  "Primary administration record stating that one interim conservation order, for protection of the night parrot, was issued during 2015-16. Used only as historical practice calibration; rarity of use is not a statutory threshold or prediction of outcome."
  Source.publicAttribution

nightParrotMedia2016 : Source.AttributedSource
nightParrotMedia2016 = Source.mkNoDOISource
  "Queensland Government — Minister for Environment and Heritage Protection and Minister for National Parks and the Great Barrier Reef"
  "More security for endangered night parrot"
  "Queensland Ministerial Media Statement"
  "2016"
  "https://statements.qld.gov.au/statements/78024"
  Source.governmentSource
  "Contemporaneous government statement identifying the night parrot habitat as subject to an interim conservation order. Used as a practice-history corroborator, not as precedent determining the Woogaroo merits."
  Source.publicAttribution

sotaExtensionAtlas : Source.AttributedSourceAtlas
sotaExtensionAtlas = Source.mkSourceAtlas
  "Woogaroo Ibrahim s102/s13 SOTA extension"
  "DASHI.Law.SensibLawWoogarooIbrahimS102S13SotaExtensionExact"
  (rus2021 ∷ dexter2018 ∷ tranMaron2024 ∷ nca105Current ∷ nightParrotAdministration2016 ∷ nightParrotMedia2016 ∷ [])
  "Empirical movement/road-risk and offsets literature plus primary s 105/practice-history sources. These sources sharpen method, counterfactual and remedy questions; none becomes same-object Springview evidence without an explicit join."

------------------------------------------------------------------------
-- Ibrahim coordinates.
------------------------------------------------------------------------

rusMovementCoordinate : Ibrahim.DashiKnowledgeCoordinate
rusMovementCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimS102S13SotaExtensionExact.agda"
  "functional-connectivity effect on koala movement and space use"
  koalaDewey
  (Id.rawItemId habitatFragmentationQid)
  "doi:10.1111/acv.12596"

dexterRoadCoordinate : Ibrahim.DashiKnowledgeCoordinate
dexterRoadCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimS102S13SotaExtensionExact.agda"
  "SEQ individual koala road-crossing behaviour"
  koalaDewey
  (Id.rawItemId koalaQid)
  "doi:10.1071/AM16043"

tranMaronOffsetCoordinate : Ibrahim.DashiKnowledgeCoordinate
tranMaronOffsetCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimS102S13SotaExtensionExact.agda"
  "national empirical audit of EPBC koala habitat offsets"
  conservationDewey
  (Id.rawItemId koalaQid)
  "doi:10.1111/csp2.13271"

s105DurationCoordinate : Ibrahim.DashiKnowledgeCoordinate
s105DurationCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimS102S13SotaExtensionExact.agda"
  "Queensland interim-conservation-order duration"
  lawDewey
  (Id.rawItemId environmentalLawQid)
  "Nature Conservation Act 1992 s 105"

nightParrotPracticeCoordinate : Ibrahim.DashiKnowledgeCoordinate
nightParrotPracticeCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimS102S13SotaExtensionExact.agda"
  "historical Queensland interim-conservation-order practice"
  lawDewey
  (Id.rawItemId endangeredSpeciesQid)
  "Queensland 2015-16 administration report + contemporaneous Ministerial statement"

------------------------------------------------------------------------
-- Traversal edges.  All new science edges are support/cross-pollination,
-- never a same-object dependency or legal promotion.
------------------------------------------------------------------------

rusToS102 : Ibrahim.DashiFirstLinkEdge
rusToS102 = Ibrahim.dashi-first-link-edge
  rusMovementCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "GPS evidence makes loss of functional connectivity a concrete movement-cost mechanism for the independent s 102 expert to test. It supplies no Springview effect size."
  true

rusToS13 : Ibrahim.DashiFirstLinkEdge
rusToS13 = Ibrahim.dashi-first-link-edge
  rusMovementCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "The study sharpens the without-site functional-connectivity counterfactual; it does not identify the local viable population or establish essentiality."
  true

dexterToS102 : Ibrahim.DashiFirstLinkEdge
dexterToS102 = Ibrahim.dashi-first-link-edge
  dexterRoadCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "SEQ evidence supports testing whether fragmentation-induced movement would alter road exposure for this landscape. Individual variability prevents transplanting the observed crossing rate to Woogaroo."
  true

s105ToS102 : Ibrahim.DashiFirstLinkEdge
s105ToS102 = Ibrahim.dashi-first-link-edge
  s105DurationCoordinate Canonical.s102StatutoryCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Section 105 constrains the temporal remedy envelope after an s 102 order is made. It does not add a merits element to s 102."
  true

nightParrotToS102 : Ibrahim.DashiFirstLinkEdge
nightParrotToS102 = Ibrahim.dashi-first-link-edge
  nightParrotPracticeCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Historical administrative practice shows the statutory mechanism has been used. It is not binding precedent and its rarity does not raise the legal threshold."
  true

------------------------------------------------------------------------
-- Legal atom intersection.
------------------------------------------------------------------------

record SotaAtomBinding : Set where
  constructor sota-atom-binding
  field
    coordinate : Ibrahim.DashiKnowledgeCoordinate
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    role : SourceRole
    locality : LocalityClass
    admissibleAsContext : Bool
    sameObjectPaid : Bool
    atomComplete : Bool
    contribution : String
    residual : String

open SotaAtomBinding public

rusEffectBinding : SotaAtomBinding
rusEffectBinding = sota-atom-binding
  rusMovementCoordinate
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  primaryEmpiricalArticle
  australianNationalComparator
  true false false
  "Supports a causal mechanism in which reduced functional connectivity changes koala movement cost and space use."
  "Independent expert still must determine whether the approved/current Woogaroo process is likely to produce a significant detrimental effect."

dexterEffectBinding : SotaAtomBinding
dexterEffectBinding = sota-atom-binding
  dexterRoadCoordinate
  Atom.likelySignificantDetrimentalEffectAtom
  Atom.nca102InterimOrderConsumer
  primaryEmpiricalArticle
  southEastQueenslandRegional
  true false false
  "Supports SEQ road-exposure as a plausible indirect/cumulative effect pathway and shows strong individual variation in crossing behaviour."
  "Acquire local movement/road/rescue evidence and avoid importing the regional crossing proportion as a Springview parameter."

rusEssentialityBinding : SotaAtomBinding
rusEssentialityBinding = sota-atom-binding
  rusMovementCoordinate
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  primaryEmpiricalArticle
  australianNationalComparator
  true false false
  "Provides a tested functional-connectivity variable for the without-site counterfactual."
  "Local viable-population identity and realised functional connectivity remain unpaid."

tranMaronOffsetBinding : SotaAtomBinding
tranMaronOffsetBinding = sota-atom-binding
  tranMaronOffsetCoordinate
  Atom.offsetBaselineRiskOfLossAtom
  Atom.epbc8575OffsetAdequacyConsumer
  crossProjectEmpiricalAudit
  australianNationalComparator
  true false false
  "Empirically identifies averted-loss optimism and double-counting as recurring failure modes in koala offset calculations."
  "Obtain the final 2019/8575 offset calculations, exact parcels, baseline risk, prior obligations and management assumptions before applying those diagnostics to this project."

------------------------------------------------------------------------
-- Remedy/practice calibration is separate from merits atoms.
------------------------------------------------------------------------

record S102RemedyCalibration : Set where
  constructor s102-remedy-calibration
  field
    ordinaryMaximumDays : String
    additionalMaximumExtensionDays : String
    extensionDecisionMaker : String
    historicalUseLocated : Bool
    historicalUseCount2015_16 : String
    historicalExample : String
    affectsMeritsThreshold : Bool
    strategyUse : String

currentS102RemedyCalibration : S102RemedyCalibration
currentS102RemedyCalibration = s102-remedy-calibration
  "60"
  "90"
  "Governor in Council by gazette notice"
  true
  "one interim conservation order reported for 2015-16"
  "night parrot protection"
  false
  "Treat s 102 as a temporary bridge requiring a downstream preservation/decision strategy. Rare historic use informs practical planning only; it is not evidence that the statutory threshold is higher than its text or that a Woogaroo request would fail."

------------------------------------------------------------------------
-- Source-dependency / Snowball result.
------------------------------------------------------------------------

record SotaSnowballFrontier : Set where
  constructor sota-snowball-frontier
  field
    newIndependentMechanismCarriers : Bool
    sameObjectEcologyAdded : Bool
    localMonitoringStillHigherAlpha : Bool
    currentIndependentExpertStillNeeded : Bool
    viablePopulationJoinStillNeeded : Bool
    finalOffsetCarrierStillNeeded : Bool
    s102DurationKnown : Bool
    s102HistoricalPracticeKnown : Bool
    nextCut : String

currentSotaSnowballFrontier : SotaSnowballFrontier
currentSotaSnowballFrontier = sota-snowball-frontier
  true false true true true true true true
  "Stop adding generic literature when it no longer changes a consumer. Highest-value next carriers remain: existing Ipswich 2020/2023/2025 monitoring results; locality-appropriate rescue/mortality/movement data; current independent ecological opinion for s 102; local viable-population/functional-connectivity join for s 13; and the final 2019/8575 offset calculation package."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

populationAtlas : Source.AttributedSourceAtlas
populationAtlas = Population.regionalPopulationSourceAtlas

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data GPSMechanismEqualsWoogarooEffect : Set where
data SEQRoadCrossingRateEqualsWoogarooRate : Set where
data OffsetAuditEqualsWoogarooOffsetInvalidity : Set where
data HistoricalUseEqualsPrecedent : Set where
data RareUseEqualsHigherStatutoryThreshold : Set where
data DurationLimitEqualsMeritsDefect : Set where
data QidEqualsSameObjectEvidence : Set where
data DeweyEqualsLegalDependency : Set where
data DoiEqualsIndependentObservation : Set where

gpsMechanismDoesNotCreateWoogarooEffect : GPSMechanismEqualsWoogarooEffect → ⊥
gpsMechanismDoesNotCreateWoogarooEffect ()

seqRateDoesNotCreateWoogarooRate : SEQRoadCrossingRateEqualsWoogarooRate → ⊥
seqRateDoesNotCreateWoogarooRate ()

offsetAuditDoesNotInvalidateWoogarooOffsets : OffsetAuditEqualsWoogarooOffsetInvalidity → ⊥
offsetAuditDoesNotInvalidateWoogarooOffsets ()

historicalUseDoesNotCreatePrecedent : HistoricalUseEqualsPrecedent → ⊥
historicalUseDoesNotCreatePrecedent ()

rareUseDoesNotRaiseTextualThreshold : RareUseEqualsHigherStatutoryThreshold → ⊥
rareUseDoesNotRaiseTextualThreshold ()

durationDoesNotDefeatMerits : DurationLimitEqualsMeritsDefect → ⊥
durationDoesNotDefeatMerits ()

qidDoesNotCreateSameObjectEvidence : QidEqualsSameObjectEvidence → ⊥
qidDoesNotCreateSameObjectEvidence ()

deweyDoesNotCreateLegalDependency : DeweyEqualsLegalDependency → ⊥
deweyDoesNotCreateLegalDependency ()

doiDoesNotCreateIndependentObservation : DoiEqualsIndependentObservation → ⊥
doiDoesNotCreateIndependentObservation ()
