module DASHI.Biology.DrosophilaSignedFibreAnatomySourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Biology.DrosophilaJoinedObserverSourceSnowballExact as JoinedSource

------------------------------------------------------------------------
-- DROSOPHILA SIGNED-FIBRE ANATOMY / TRANSMITTER SOURCE SNOWBALL
--
-- This owner keeps four layers separate:
--   1. MaleCNS body-level transmitter predictions / annotations;
--   2. the dashiBRAIN coarse sign convention used for a benchmark feature;
--   3. primary literature about particular Drosophila transmitter/circuit facts;
--   4. local regional sender-scalar observations.
--
-- Literature context may support interpretation, but does not validate a local
-- sender scalar merely because a neuropil name sounds compatible with a paper.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Drosophila signed-fibre anatomy snowball"
  "verified external concept identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity checked 2026-09-11; external identity does not establish local MaleCNS scalar value, causal sign, receptor action, or same-cell correspondence")

drosophilaMelanogasterQid : Identity.ExternalIdentityDemand
drosophilaMelanogasterQid = mkQid "Drosophila melanogaster" "Q130888"

neurotransmitterQid : Identity.ExternalIdentityDemand
neurotransmitterQid = mkQid "neurotransmitter" "Q162657"

acetylcholineQid : Identity.ExternalIdentityDemand
acetylcholineQid = mkQid "acetylcholine" "Q180623"

gabaQid : Identity.ExternalIdentityDemand
gabaQid = mkQid "gamma-aminobutyric acid / GABA" "Q210021"

record SignedFibreDeweyCoordinate : Set where
  constructor signed-fibre-dewey-coordinate
  field
    subject : String
    dewey : String
    verification : String
    createsEmpiricalAuthority : Bool
open SignedFibreDeweyCoordinate public

neuroscienceDewey : SignedFibreDeweyCoordinate
neuroscienceDewey = signed-fibre-dewey-coordinate
  "neuroscience / nervous-system physiology"
  "612.8"
  "retained as the existing DASHI narrow neuroscience candidate"
  false

acetylcholineDewey : SignedFibreDeweyCoordinate
acetylcholineDewey = signed-fibre-dewey-coordinate
  "acetylcholine"
  "612.8042"
  "Wikidata Q180623 DDC statement inspected 2026-09-11"
  false

gabaDewey : SignedFibreDeweyCoordinate
gabaDewey = signed-fibre-dewey-coordinate
  "GABA"
  "unresolved"
  "no exact inspected DDC statement promoted in this pass"
  false

------------------------------------------------------------------------
-- Primary/source-bounded lineage.
------------------------------------------------------------------------

ecksteinNeurotransmitterClassification : Attribution.AttributedSource
ecksteinNeurotransmitterClassification = Attribution.mkDOISource
  "Nils Eckstein; Alexander Bates; et al."
  "Neurotransmitter classification from electron microscopy images at synaptic sites in Drosophila melanogaster"
  "Cell 187(10), 2574-2594.e23"
  "2024"
  "10.1016/j.cell.2024.03.016"
  "https://doi.org/10.1016/j.cell.2024.03.016"
  Attribution.academicArticleSource
  "primary transmitter-classification source: predicts six transmitter classes from EM; prediction identity is distinct from receptor-resolved synaptic effect"
  Attribution.publicAttribution

barnstedtKenyonOutput : Attribution.AttributedSource
barnstedtKenyonOutput = Attribution.mkDOISource
  "Oliver Barnstedt; David Owald; et al."
  "Memory-Relevant Mushroom Body Output Synapses Are Cholinergic"
  "Neuron 89(6), 1237-1247"
  "2016"
  "10.1016/j.neuron.2016.02.015"
  "https://doi.org/10.1016/j.neuron.2016.02.015"
  Attribution.academicArticleSource
  "primary experimental source that Drosophila Kenyon-cell output uses acetylcholine; it does not assign the local MaleCNS aL/bL/gL/PED sender-scalar values"
  Attribution.publicAttribution

yasuyamaAntennalLobeRelay : Attribution.AttributedSource
yasuyamaAntennalLobeRelay = Attribution.mkDOISource
  "Kouji Yasuyama; Ian A. Meinertzhagen; Friedrich-Wilhelm Schuermann"
  "Synaptic connections of cholinergic antennal lobe relay neurons innervating the lateral horn neuropile in the brain of Drosophila melanogaster"
  "Journal of Comparative Neurology 466, 299-315"
  "2003"
  "10.1002/cne.10867"
  "https://doi.org/10.1002/cne.10867"
  Attribution.academicArticleSource
  "primary anatomical source for cholinergic antennal-lobe relay neurons; not proof that every AL neuron or every outgoing AL connection is cholinergic"
  Attribution.publicAttribution

xieRingNeuronGaba : Attribution.AttributedSource
xieRingNeuronGaba = Attribution.mkDOISource
  "Xiaojun Xie; Masashi Tabuchi; Matthew P. Brown; Sarah P. Mitchell; Mark N. Wu; Alex L. Kolodkin"
  "The laminar organization of the Drosophila ellipsoid body is semaphorin-dependent and prevents the formation of ectopic synaptic connections"
  "eLife 6:e25328"
  "2017"
  "10.7554/eLife.25328"
  "https://doi.org/10.7554/eLife.25328"
  Attribution.academicArticleSource
  "primary experimental source showing GABA/GABA-A organization in ring-neuron ellipsoid-body circuitry whose dendrites occupy the bulb; not proof that the whole BU neuropil is an exclusively inhibitory sender population"
  Attribution.publicAttribution

maleCnsPrimary : JoinedSource.SnowballSourceReceipt
maleCnsPrimary = JoinedSource.maleCnsConnectome

------------------------------------------------------------------------
-- Local benchmark sign convention: source code, not a universal physiology law.
------------------------------------------------------------------------

record BenchmarkSignConvention : Set where
  constructor benchmark-sign-convention
  field
    producerRepository : String
    producerCommit : String
    producerPath : String
    acetylcholineSign : String
    gabaSign : String
    glutamateSign : String
    modulatorFallback : String
    receptorResolved : Bool
    globallyFixedPostsynapticEffectClaim : Bool
open BenchmarkSignConvention public

currentBenchmarkSignConvention : BenchmarkSignConvention
currentBenchmarkSignConvention = benchmark-sign-convention
  "github.com/chboishabba/dashiBRAIN"
  "817689a1b0b2403513fdcd329ba8f264551a091d"
  "dashi/io/malecns_loader.py::infer_transmitter_sign"
  "+1"
  "-1"
  "-1"
  "+1 unless later receptor-aware model supplied"
  false
  false

record SignedFibreAnatomySourceBoundary : Set where
  constructor signed-fibre-anatomy-source-boundary
  field
    primaryLiteratureRetained : Bool
    canonicalDoiLinksRetained : Bool
    qidsAreIdentityCoordinatesOnly : Bool
    deweyIsNavigationOnly : Bool
    transmitterPredictionEqualsReceptorResolvedEffect : Bool
    benchmarkSignConventionEqualsUniversalPhysiology : Bool
    namedNeuropilLiteratureAutomaticallyValidatesLocalScalar : Bool
    bulbLiteratureSupportsWholeBulbExclusiveInhibitionClaim : Bool
open SignedFibreAnatomySourceBoundary public

canonicalSignedFibreAnatomySourceBoundary : SignedFibreAnatomySourceBoundary
canonicalSignedFibreAnatomySourceBoundary = signed-fibre-anatomy-source-boundary
  true true true true false false false false
