module DASHI.Law.SensibLawWoogarooINaturalistCorpusSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Saved iNaturalist pages supplied by the observer are treated as a corpus.
-- Counts are by unique native observation id, never by HTML card/reference
-- count. Quality grade and locality are retained as independent coordinates.
------------------------------------------------------------------------

record INaturalistCorpusReceipt : Set where
  constructor inaturalist-corpus-receipt
  field
    observerHandle : String
    savedCarrierCount : Nat
    uniqueObservationCount : Nat
    researchGradeCount : Nat
    needsIdCount : Nat
    casualCount : Nat
    localClusterCount : Nat
    localClusterDefinition : String
    deduplicationRule : String
    attribution : String
    residual : String

open INaturalistCorpusReceipt public

johl1SavedCorpus : INaturalistCorpusReceipt
johl1SavedCorpus = inaturalist-corpus-receipt
  "johl1"
  3
  114
  36
  46
  32
  76
  "Saved locality labels containing Brookwater, Springfield, Springfield Central, Spring Mountain, Augustine Heights, or Bellbird Park."
  "Deduplicate by native iNaturalist observation id across the three saved observation HTML pages; duplicate cards/references do not create independent observations."
  "Observer-supplied saved iNaturalist pages; page metadata identifies the collection as observations by Johl Brown / user_id=johl1. Counts are DASHI reconstruction from those saved carriers, not an iNaturalist-issued statistical statement."
  "Perform per-observation Snowball ingestion for local records; join exact public coordinates/accuracy circles and conservation status only from each native observation record or other attributed source."

record PageRecoveryReceipt : Set where
  constructor page-recovery-receipt
  field
    pageLabel : String
    uniqueIdsOnPage : Nat
    newIdsBeyondPriorPages : Nat
    boundedReading : String

open PageRecoveryReceipt public

savedPageOne : PageRecoveryReceipt
savedPageOne = page-recovery-receipt
  "Observations · iNaturalist.html"
  24
  24
  "Partial saved page; its ids are subsumed by the later 96-observation page and therefore do not add 24 independent corpus records."

savedPageTwo : PageRecoveryReceipt
savedPageTwo = page-recovery-receipt
  "Observations · iNaturalist2.html"
  96
  96
  "Main saved table/map carrier previously analysed."

savedPageThree : PageRecoveryReceipt
savedPageThree = page-recovery-receipt
  "Observations · iNaturalist3.html"
  19
  18
  "Recovered from the supplied tar.xz with its website assets; contains 18 observation ids not present on saved page two and one overlap."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HTMLReferenceCountIsObservationCount : Set where

data DuplicateSavedPageIsIndependentCorroboration : Set where

data ResearchGradeIsAgencyFinding : Set where

data LocalityLabelIsExactProjectIntersection : Set where

data ObservationCountPaysLegalElement : Set where

data NeedsIDIsConfirmedTaxon : Set where

noReferenceCountCollapse : HTMLReferenceCountIsObservationCount → ⊥
noReferenceCountCollapse ()

noSavedPageCorroborationCollapse : DuplicateSavedPageIsIndependentCorroboration → ⊥
noSavedPageCorroborationCollapse ()

noResearchAgencyCollapse : ResearchGradeIsAgencyFinding → ⊥
noResearchAgencyCollapse ()

noLocalityIntersectionCollapse : LocalityLabelIsExactProjectIntersection → ⊥
noLocalityIntersectionCollapse ()

noCountLegalCollapse : ObservationCountPaysLegalElement → ⊥
noCountLegalCollapse ()

noNeedsIdConfirmationCollapse : NeedsIDIsConfirmedTaxon → ⊥
noNeedsIdConfirmationCollapse ()

record INaturalistCorpusPolicy : Set where
  constructor inaturalist-corpus-policy
  field
    deduplicateByNativeObservationId : Bool
    preserveQualityGrade : Bool
    preserveLocalitySeparately : Bool
    preservePerObservationAttribution : Bool
    prohibitDuplicateCorroboration : Bool
    prohibitAutomaticLegalPromotion : Bool

canonicalINaturalistCorpusPolicy : INaturalistCorpusPolicy
canonicalINaturalistCorpusPolicy = inaturalist-corpus-policy
  true true true true true true
