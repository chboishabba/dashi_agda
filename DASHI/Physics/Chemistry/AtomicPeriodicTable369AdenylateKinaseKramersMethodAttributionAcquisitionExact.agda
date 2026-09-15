module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseKramersMethodAttributionAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact as Figure5
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionExact as Figure6

------------------------------------------------------------------------
-- ATTRIBUTED KRAMERS-METHOD ACQUISITION
--
-- The Figure-5/Figure-6 directed rate numerics are already paid by same-object
-- source-image/PDF readout.  This owner acquires the *method provenance* behind
-- their rate role without changing those printed cells:
--
--   Li-Liu-Ji 2015 reports the AdK-specific free-energy landscape, diffusion
--   calibration and Kramers-derived arrow labels;
--   Hänggi-Talkner-Borkovec 1990 is the cited general reaction-rate-theory
--   source (reference 88);
--   Sriraman-Kevrekidis-Hummer 2005 and Hummer 2005 are the cited diffusion/
--   Bayesian-analysis method sources (references 89 and 90).
--
-- General method citations do not pay an AdK number, validate a reaction
-- coordinate, or turn a calculated Kramers rate into an experimental rate.
------------------------------------------------------------------------

liLiuJiSource : Attribution.AttributedSource
liLiuJiSource = Sparse.liLiuJi2015Source

liLiuJiReceipt : Snowball.SourceRoleSnowballReceipt liLiuJiSource
liLiuJiReceipt = Snowball.canonicalSourceRoleSnowballReceipt liLiuJiSource

hanggi1990Source : Attribution.AttributedSource
hanggi1990Source =
  Attribution.mkDOISource
    "Peter Hanggi, Peter Talkner and Michal Borkovec"
    "Reaction-rate theory: fifty years after Kramers"
    "Reviews of Modern Physics"
    "1990"
    "10.1103/RevModPhys.62.251"
    "https://doi.org/10.1103/RevModPhys.62.251"
    Attribution.academicArticleSource
    "general reaction-rate-theory source cited as reference 88 by Li-Liu-Ji; it supplies methodological background only, not AdK-specific rate numerics or experimental validation"
    Attribution.publicAttribution

hanggi1990Receipt : Snowball.SourceRoleSnowballReceipt hanggi1990Source
hanggi1990Receipt = Snowball.canonicalSourceRoleSnowballReceipt hanggi1990Source

sriramanKevrekidisHummer2005Source : Attribution.AttributedSource
sriramanKevrekidisHummer2005Source =
  Attribution.mkDOISource
    "Saravanapriyan Sriraman, Ioannis G. Kevrekidis and Gerhard Hummer"
    "Coarse Master Equation from Bayesian Analysis of Replica Molecular Dynamics Simulations"
    "Journal of Physical Chemistry B"
    "2005"
    "10.1021/jp046448u"
    "https://doi.org/10.1021/jp046448u"
    Attribution.academicArticleSource
    "general Bayesian coarse-rate/diffusion methodology cited as reference 89 by Li-Liu-Ji; it does not itself pay the AdK diffusion coefficient"
    Attribution.publicAttribution

sriramanReceipt : Snowball.SourceRoleSnowballReceipt sriramanKevrekidisHummer2005Source
sriramanReceipt = Snowball.canonicalSourceRoleSnowballReceipt sriramanKevrekidisHummer2005Source

hummer2005Source : Attribution.AttributedSource
hummer2005Source =
  Attribution.mkDOISource
    "Gerhard Hummer"
    "Position-dependent diffusion coefficients and free energies from Bayesian analysis of equilibrium and replica molecular dynamics simulations"
    "New Journal of Physics"
    "2005"
    "10.1088/1367-2630/7/1/034"
    "https://doi.org/10.1088/1367-2630/7/1/034"
    Attribution.academicArticleSource
    "general diffusion/free-energy inference methodology cited as reference 90 by Li-Liu-Ji; it does not itself pay the AdK diffusion coefficient"
    Attribution.publicAttribution

hummerReceipt : Snowball.SourceRoleSnowballReceipt hummer2005Source
hummerReceipt = Snowball.canonicalSourceRoleSnowballReceipt hummer2005Source

------------------------------------------------------------------------
-- External-identity demands.  DOI/PMID/QID are navigation/provenance only.
------------------------------------------------------------------------

hanggiDOI : Identity.ExternalIdentityDemand
hanggiDOI = Identity.mkOptionalIdentityDemand
  "AdK Kramers method attribution"
  "Hänggi-Talkner-Borkovec DOI"
  "Reaction-rate theory: fifty years after Kramers"
  Identity.doi
  (Identity.verified "DOI" "10.1103/RevModPhys.62.251")

hanggiArticleQID : Identity.ExternalIdentityDemand
hanggiArticleQID = Identity.mkOptionalIdentityDemand
  "AdK Kramers method attribution"
  "Hänggi-Talkner-Borkovec article Wikidata identity"
  "Reaction-rate theory: fifty years after Kramers"
  Identity.wikidataQid
  (Identity.unresolved "article-level QID not verified in the acquisition pass")

sriramanDOI : Identity.ExternalIdentityDemand
sriramanDOI = Identity.mkOptionalIdentityDemand
  "AdK diffusion-method attribution"
  "Sriraman-Kevrekidis-Hummer DOI"
  "Coarse Master Equation from Bayesian Analysis of Replica Molecular Dynamics Simulations"
  Identity.doi
  (Identity.verified "DOI" "10.1021/jp046448u")

sriramanPMID : Identity.ExternalIdentityDemand
sriramanPMID = Identity.mkOptionalIdentityDemand
  "AdK diffusion-method attribution"
  "Sriraman-Kevrekidis-Hummer PubMed identity"
  "Coarse Master Equation from Bayesian Analysis of Replica Molecular Dynamics Simulations"
  Identity.officialIdentifier
  (Identity.verified "PubMed" "16851726")

hummerDOI : Identity.ExternalIdentityDemand
hummerDOI = Identity.mkOptionalIdentityDemand
  "AdK diffusion-method attribution"
  "Hummer 2005 DOI"
  "Position-dependent diffusion coefficients and free energies from Bayesian analysis of equilibrium and replica molecular dynamics simulations"
  Identity.doi
  (Identity.verified "DOI" "10.1088/1367-2630/7/1/034")

------------------------------------------------------------------------
-- Source-role acquisition receipts for the two AdK contexts.
------------------------------------------------------------------------

data AdKRateContext : Set where
  ligandFreeFigureFive : AdKRateContext
  ligandBoundFigureSix : AdKRateContext

record KramersRateMethodReceipt : Set where
  constructor kramers-rate-method-receipt
  field
    context : AdKRateContext
    reportingSource : Attribution.AttributedSource
    generalRateTheorySource : Attribution.AttributedSource
    diffusionInferenceSourceOne : Attribution.AttributedSource
    diffusionInferenceSourceTwo : Attribution.AttributedSource
    sourceLocator : String
    rateDisplayUnit : String
    diffusionCoefficientReading : String
    numericRateManifestation : String
    rateKind : String
    methodRolePaid : Bool
    exactFigureRateNumericsPaid : Bool
    experimentallyMeasuredRate : Bool
    interpretation : String
open KramersRateMethodReceipt public

apoKramersMethodReceipt : KramersRateMethodReceipt
apoKramersMethodReceipt = kramers-rate-method-receipt
  ligandFreeFigureFive
  liLiuJiSource
  hanggi1990Source
  sriramanKevrekidisHummer2005Source
  hummer2005Source
  "Li-Liu-Ji Figure 5 caption -> Text S3 -> refs 88-90"
  "10^-2 ns^-1"
  "D approximately 4.47 x 10^-3 rad^2/ns, determined from LT-MD simulations"
  Figure5.figureFivePanelCLocator
  "Kramers-derived transition-rate constants calculated from the AdK free-energy landscape with the source-reported diffusion calibration"
  true true false
  "method provenance and same-object Figure-5 numerics are both retained; the general method papers do not own the AdK numeric cells"

boundKramersMethodReceipt : KramersRateMethodReceipt
boundKramersMethodReceipt = kramers-rate-method-receipt
  ligandBoundFigureSix
  liLiuJiSource
  hanggi1990Source
  sriramanKevrekidisHummer2005Source
  hummer2005Source
  "Li-Liu-Ji Figure 6 caption -> Text S3 -> refs 88-90"
  "10^-2 ns^-1"
  "D approximately 5.13 x 10^-4 rad^2/ns, determined from LT-MD simulations"
  Figure6.figureSixPanelCLocator
  "Kramers-derived transition-rate constants calculated from the ligand-bound AdK free-energy landscape with the source-reported diffusion calibration"
  true true false
  "method provenance and same-object Figure-6 numerics are both retained; the general method papers do not own the AdK numeric cells"

apoDirectedRates = Figure5.directedRates
boundDirectedRates = Figure6.directedRates

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data GeneralKramersTheoryCreatesAdkRateNumeral : Set where
data DiffusionMethodCitationCreatesAdkDiffusionCoefficient : Set where
data DiffusionCoefficientAloneDeterminesTransitionRate : Set where
data KramersCalculatedRateIsExperimentalRate : Set where
data MethodCitationValidatesAdkReactionCoordinateAssumptions : Set where

generalTheoryDoesNotCreateAdkRateNumeral : GeneralKramersTheoryCreatesAdkRateNumeral → ⊥
generalTheoryDoesNotCreateAdkRateNumeral ()

diffusionMethodCitationDoesNotCreateAdkCoefficient : DiffusionMethodCitationCreatesAdkDiffusionCoefficient → ⊥
diffusionMethodCitationDoesNotCreateAdkCoefficient ()

diffusionCoefficientAloneDoesNotDetermineRate : DiffusionCoefficientAloneDeterminesTransitionRate → ⊥
diffusionCoefficientAloneDoesNotDetermineRate ()

kramersCalculatedRateDoesNotBecomeExperimental : KramersCalculatedRateIsExperimentalRate → ⊥
kramersCalculatedRateDoesNotBecomeExperimental ()

methodCitationDoesNotValidateAdkCoordinates : MethodCitationValidatesAdkReactionCoordinateAssumptions → ⊥
methodCitationDoesNotValidateAdkCoordinates ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKKramersMethodAttributionBoundary : Set where
  constructor adk-kramers-method-attribution-boundary
  field
    liLiuJiOwnsAdkRateReadout : Bool
    hanggiRateTheoryIdentityPaid : Bool
    sriramanDiffusionMethodIdentityPaid : Bool
    hummerDiffusionMethodIdentityPaid : Bool
    apoDiffusionCoefficientRolePaid : Bool
    boundDiffusionCoefficientRolePaid : Bool
    fullFigureFiveRateNumericsRetained : Bool
    fullFigureSixRateNumericsRetained : Bool
    generalTheoryCreatesAdkNumerics : Bool
    diffusionCitationCreatesAdkCoefficient : Bool
    diffusionCoefficientAloneDeterminesRate : Bool
    kramersRateEqualsExperimentalRate : Bool
    methodCitationValidatesReactionCoordinate : Bool
    unresolvedMethodArticleQidBlocksMethodRole : Bool
open AdKKramersMethodAttributionBoundary public

canonicalAdKKramersMethodAttributionBoundary : AdKKramersMethodAttributionBoundary
canonicalAdKKramersMethodAttributionBoundary = adk-kramers-method-attribution-boundary
  true true true true true true true true
  false false false false false false
