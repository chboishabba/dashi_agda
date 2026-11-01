module DASHI.Biology.Agriculture.AustralianPostFireAcaciaBNFObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES

------------------------------------------------------------------------
-- AUSTRALIAN POST-FIRE ACACIA BNF OBSERVER / ISOTOPE CALIBRATION
--
-- Natural-abundance and enriched-15N approaches are not treated as a
-- context-free measurement token.  Baseline homogeneity, reference-plant
-- identity, fire history, site, sampling scope and plant compartment remain
-- part of measurement adequacy.
------------------------------------------------------------------------

hamiltonEtAl1993DOI : String
hamiltonEtAl1993DOI = "10.1016/0378-1127(93)90119-8"

guintoEtAl2000DOI : String
guintoEtAl2000DOI = "10.1139/x99-183"

hamiltonEtAl1993 : Attribution.AttributedSource
hamiltonEtAl1993 = Attribution.mkDOISource
  "S. D. Hamilton; P. Hopmans; P. M. Chalk; C. J. Smith"
  "Field estimation of N2 fixation by Acacia spp. using 15N isotope dilution and labelling with 35S"
  "Forest Ecology and Management 56(1-4):297-313"
  "1993"
  hamiltonEtAl1993DOI
  "https://doi.org/10.1016/0378-1127(93)90119-8"
  Attribution.academicArticleSource
  "Australian mixed-eucalypt-forest field study estimating fixation by understorey Acacia melanoxylon and Acacia mucronata for 27 months after prescribed fire. Natural-abundance and 15N-enriched isotope-dilution approaches were compared, with native Poa sieberiana and opportunistic non-fixing plants as references. Natural abundance was considered usable in that site because soil/reference enrichment was sufficiently uniform; fixation per plant increased through time while ecosystem accretion remained density constrained."
  Attribution.publicAttribution

guintoEtAl2000 : Attribution.AttributedSource
guintoEtAl2000 = Attribution.mkDOISource
  "Danilo F. Guinto; Zhihong Xu; Alan P. N. House; Paul G. Saffigna"
  "Assessment of N2 fixation by understorey acacias in recurrently burnt eucalypt forests of subtropical Australia using 15N isotope dilution techniques"
  "Canadian Journal of Forest Research 30(1):112-121"
  "2000"
  guintoEtAl2000DOI
  "https://doi.org/10.1139/x99-183"
  Attribution.academicArticleSource
  "Subtropical Australian recurrent-fire study. Natural-abundance delta-15N variation among established Acacia/reference plants was too large for a fixation estimate in the first study. In the enriched-15N glasshouse study using soils from fire-frequency plots, estimated whole-plant Ndfa changed with fire treatment and with reference-plant identity. The source therefore makes observer/reference design part of the evidence state."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Observer roles.
------------------------------------------------------------------------

data PostFireObserverRole : Set where
  fieldNaturalAbundanceAndDilutionComparison : PostFireObserverRole
  recurrentFireNaturalAbundanceFailure : PostFireObserverRole
  enrichedIsotopeReferenceSensitivity : PostFireObserverRole

record PostFireObserverReceipt : Set where
  constructor post-fire-observer-receipt
  field
    source : Attribution.AttributedSource
    sourceDOI : String
    role : PostFireObserverRole
    targetReading : String
    baselineReading : String
    referenceReading : String
    fireSiteReading : String
    boundedReading : String
open PostFireObserverReceipt public

hamiltonObserverReceipt : PostFireObserverReceipt
hamiltonObserverReceipt = post-fire-observer-receipt
  hamiltonEtAl1993
  hamiltonEtAl1993DOI
  fieldNaturalAbundanceAndDilutionComparison
  "Acacia melanoxylon and Acacia mucronata over 27 months after fire"
  "natural-15N enrichment judged sufficiently uniform in this site/context"
  "native Poa sieberiana plus opportunistic non-fixing reference species"
  "mixed eucalypt forest after prescribed fire"
  "site-specific adequacy of natural abundance does not become a universal method theorem"

guintoNaturalAbundanceReceipt : PostFireObserverReceipt
guintoNaturalAbundanceReceipt = post-fire-observer-receipt
  guintoEtAl2000
  guintoEtAl2000DOI
  recurrentFireNaturalAbundanceFailure
  "established understorey Acacia in dry and wet recurrently burnt eucalypt forest"
  "substantial plant/reference delta-15N variation prevented natural-abundance fixation evaluation"
  "multiple nonlegume reference species"
  "fire-frequency plots at distinct dry/wet forest sites"
  "natural-abundance estimator adequacy failed under this baseline geometry"

guintoReferenceSensitivityReceipt : PostFireObserverReceipt
guintoReferenceSensitivityReceipt = post-fire-observer-receipt
  guintoEtAl2000
  guintoEtAl2000DOI
  enrichedIsotopeReferenceSensitivity
  "Acacia leiocalyx and Acacia oshanesii seedlings grown in soils from fire plots"
  "15N-enriched isotope-dilution experiment"
  "Ndfa estimates varied according to reference species used"
  "unburnt versus periodically/annually/biennially/quadrennially burnt soil contexts"
  "reference identity and fire treatment remain part of the estimator state"

------------------------------------------------------------------------
-- Finite observer-information-loss witness.
------------------------------------------------------------------------

data ObserverWorld : Set where
  naturalAbundanceUniformBaseline : ObserverWorld
  naturalAbundanceHeterogeneousBaseline : ObserverWorld

data ObserverTask : Set where
  adequateNdfaEstimatorTask : ObserverTask

data MethodToken : Set where
  naturalAbundance15NMethod : MethodToken

methodNameOnly : ObserverWorld → MethodToken
methodNameOnly _ = naturalAbundance15NMethod

estimatorAdequacy : ObserverTask → ObserverWorld → Bool
estimatorAdequacy adequateNdfaEstimatorTask naturalAbundanceUniformBaseline = true
estimatorAdequacy adequateNdfaEstimatorTask naturalAbundanceHeterogeneousBaseline = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

methodNameNotTaskSufficient :
  LES.TaskFactorisation methodNameOnly estimatorAdequacy → ⊥
methodNameNotTaskSufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor adequateNdfaEstimatorTask
      {naturalAbundanceUniformBaseline} {naturalAbundanceHeterogeneousBaseline} refl)

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record PostFireObserverBoundary : Set where
  constructor post-fire-observer-boundary
  field
    naturalAbundanceMethodNameImpliesAdequateEstimator : Bool
    baselineHomogeneityMayBeDropped : Bool
    referencePlantIdentityMayBeDropped : Bool
    fireFrequencyAndSiteMayBeDropped : Bool
    plantCompartmentAndSamplingScopeMayBeDropped : Bool
    percentNdfaImpliesDirectFixedNFlux : Bool
    methodAgreementAtOneSiteImpliesUniversalMethodAgreement : Bool
    referencePlantSensitivityMayBeDiscardedAsNoise : Bool
    naturalAbundanceFailureInvalidatesAll15NMethods : Bool
    enrichedIsotopeEstimateCreatesDeploymentAuthority : Bool
    sourceObservationsAreSyntheticDASHIWorlds : Bool
open PostFireObserverBoundary public

canonicalPostFireObserverBoundary : PostFireObserverBoundary
canonicalPostFireObserverBoundary = post-fire-observer-boundary
  false false false false false false false false false false false

attributionRule : String
attributionRule =
  "Hamilton et al. 1993 (DOI 10.1016/0378-1127(93)90119-8) owns its 27-month post-fire Acacia field fixation-estimation and isotope-method-comparison propositions. Guinto et al. 2000 (DOI 10.1139/x99-183) owns its recurrent-fire natural-abundance failure and enriched-15N/reference-sensitivity propositions. DASHI owns only the observer-state separation, finite TaskFactorisation witness and no-promotion boundary. Method labels, Ndfa percentages and reference-plant choices are not promoted to context-free measurement adequacy, direct fixed-N flux or deployment authority."
