module DASHI.Biology.Evolution.EvolutionaryGenomeTopologyIrreversibilityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Biology.SpectralReachabilityComplexityExact as Reach

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Darrin T. Schultz; Arno Blümel; Dalila Destanović; Fatih Sarigol;
-- Oleg Simakov (2026),
-- "Topological mixing and irreversibility in animal chromosome evolution",
-- Science Advances 12(34), eadz5561.
-- DOI: 10.1126/sciadv.adz5561
-- https://doi.org/10.1126/sciadv.adz5561
--
-- Reported source-level observations used here:
--
-- * 5,821 chromosome-scale genomes, 4,454 species, 19 animal phyla;
-- * a multiscale "evolutionary genome topology" representation that retains
--   chromosomal and subchromosomal organisation;
-- * all 406 pairwise fusions among 29 reconstructed ancestral animal linkage
--   groups are represented in sampled metazoan diversity;
-- * the full within-chromosome combinatorial potential is far from exhausted;
-- * chromosomal consolidation, dissociation, and especially fusion-with-mixing
--   generate long-lived architecture states whose history can be irreversible;
-- * accumulated mixed states place clades in distinct regions of genome-
--   architecture space and constrain the paths visible in extant diversity.
--
-- DASHI CONTRIBUTION
--
-- This module does NOT reimplement the paper's genomic pipeline or manifold
-- inference.  It extracts three generic theorem surfaces suggested by it:
--
--   (1) evolutionary architecture is naturally a directed reachability object;
--   (2) an irreversible history marker can block reverse reachability;
--   (3) a coarse observable such as chromosome count need not determine the
--       finer history-bearing architecture state.
--
-- The concrete three-state transition system below is a schematic DASHI witness
-- of those logical distinctions, not a claim that these three constructors are
-- literal biological stages observed by Schultz et al.
------------------------------------------------------------------------

canonicalTitle : String
canonicalTitle = "Topological mixing and irreversibility in animal chromosome evolution"

canonicalAuthors : List String
canonicalAuthors =
  "Darrin T. Schultz" ∷
  "Arno Blümel" ∷
  "Dalila Destanović" ∷
  "Fatih Sarigol" ∷
  "Oleg Simakov" ∷ []

canonicalDOI : String
canonicalDOI = "10.1126/sciadv.adz5561"

canonicalDOIURL : String
canonicalDOIURL = "https://doi.org/10.1126/sciadv.adz5561"

canonicalJournal : String
canonicalJournal = "Science Advances"

canonicalVolumeIssue : String
canonicalVolumeIssue = "12(34)"

canonicalArticleNumber : String
canonicalArticleNumber = "eadz5561"

canonicalYear : Nat
canonicalYear = 2026

sampledChromosomeScaleGenomes : Nat
sampledChromosomeScaleGenomes = 5821

sampledSpecies : Nat
sampledSpecies = 4454

sampledAnimalPhyla : Nat
sampledAnimalPhyla = 19

ancestralAnimalLinkageGroups : Nat
ancestralAnimalLinkageGroups = 29

sampledPairwiseAncestralFusions : Nat
sampledPairwiseAncestralFusions = 406

record SourceAttribution : Set where
  constructor sourceAttribution
  field
    title : String
    authors : List String
    doi : String
    doiURL : String
    journal : String
    volumeIssue : String
    articleNumber : String
    year : Nat

open SourceAttribution public

canonicalSourceAttribution : SourceAttribution
canonicalSourceAttribution =
  sourceAttribution
    canonicalTitle
    canonicalAuthors
    canonicalDOI
    canonicalDOIURL
    canonicalJournal
    canonicalVolumeIssue
    canonicalArticleNumber
    canonicalYear

------------------------------------------------------------------------
-- Multiscale observer interface.
--
-- The source's evolutionary genome topology simultaneously represents
-- chromosome-level and subchromosome-level organisation.  DASHI therefore
-- types the observation as a pair of views rather than collapsing the source
-- to chromosome number alone.
------------------------------------------------------------------------

record MultiscaleGenomeObserver (State : Set) : Set₁ where
  constructor multiscaleGenomeObserver
  field
    ChromosomalView : Set
    SubchromosomalView : Set
    observeChromosomal : State → ChromosomalView
    observeSubchromosomal : State → SubchromosomalView

open MultiscaleGenomeObserver public

------------------------------------------------------------------------
-- Schematic history-bearing architecture witness.
------------------------------------------------------------------------

data GenomeArchitecture : Set where
  ancestralSeparated : GenomeArchitecture
  fusedAndMixed : GenomeArchitecture
  postMixDissociated : GenomeArchitecture

-- A deliberately coarse shadow.  The first and third states have the same
-- chromosome-count class despite different history-bearing architecture.
data ChromosomeCountShadow : Set where
  oneChromosome twoChromosomes : ChromosomeCountShadow

chromosomeCountShadow : GenomeArchitecture → ChromosomeCountShadow
chromosomeCountShadow ancestralSeparated = twoChromosomes
chromosomeCountShadow fusedAndMixed = oneChromosome
chromosomeCountShadow postMixDissociated = twoChromosomes

-- The permanent-history bit is finer than the count shadow.
data MixingHistory : Set where
  noRecordedMixing recordedMixing : MixingHistory

mixingHistory : GenomeArchitecture → MixingHistory
mixingHistory ancestralSeparated = noRecordedMixing
mixingHistory fusedAndMixed = recordedMixing
mixingHistory postMixDissociated = recordedMixing

sameChromosomeCountDifferentHistory :
  chromosomeCountShadow ancestralSeparated
  ≡ chromosomeCountShadow postMixDissociated
sameChromosomeCountDifferentHistory = refl

mixingHistoriesDiffer :
  ¬ (mixingHistory ancestralSeparated ≡ mixingHistory postMixDissociated)
mixingHistoriesDiffer ()

-- A projection determines history only if equal coarse observations force equal
-- history markers.  The witness above refutes that property exactly.
CountShadowDeterminesHistory : Set
CountShadowDeterminesHistory =
  (x y : GenomeArchitecture) →
  chromosomeCountShadow x ≡ chromosomeCountShadow y →
  mixingHistory x ≡ mixingHistory y

chromosomeCountDoesNotDetermineHistory :
  ¬ CountShadowDeterminesHistory
chromosomeCountDoesNotDetermineHistory determines =
  mixingHistoriesDiffer
    (determines ancestralSeparated postMixDissociated refl)

------------------------------------------------------------------------
-- Directed transition system.
--
-- The constructors encode only the forward schematic lane.  In particular,
-- dissociation can restore the coarse chromosome-count class without erasing
-- the recorded mixing history.
------------------------------------------------------------------------

data ArchitectureStep : GenomeArchitecture → GenomeArchitecture → Set where
  fusionWithMixing :
    ArchitectureStep ancestralSeparated fusedAndMixed
  dissociationAfterMixing :
    ArchitectureStep fusedAndMixed postMixDissociated

canonicalHighway :
  Reach.ReachIn ArchitectureStep 2
    ancestralSeparated postMixDissociated
canonicalHighway =
  Reach.reachStep fusionWithMixing
    (Reach.reachStep dissociationAfterMixing Reach.reachZero)

-- There is no finite path back to the pre-mixing state in this schematic
-- transition system.  This is the exact directed-reachability content of the
-- witness; it is intentionally weaker than claiming that every real genomic
-- rearrangement is globally irreversible.
noReverseHighway :
  ∀ {n} →
  ¬ Reach.ReachIn ArchitectureStep n
      postMixDissociated ancestralSeparated
noReverseHighway ()

-- Likewise there is no single reverse fusion-with-mixing transition.
noImmediateUnmixing :
  ¬ ArchitectureStep fusedAndMixed ancestralSeparated
noImmediateUnmixing ()

------------------------------------------------------------------------
-- History-sensitive observation is strictly more informative than count alone
-- for this witness pair.
------------------------------------------------------------------------

record CountAndHistoryObservation : Set where
  constructor countAndHistoryObservation
  field
    count : ChromosomeCountShadow
    history : MixingHistory

observeCountAndHistory : GenomeArchitecture → CountAndHistoryObservation
observeCountAndHistory state =
  countAndHistoryObservation
    (chromosomeCountShadow state)
    (mixingHistory state)

record SourceClaimScope : Set where
  constructor sourceClaimScope
  field
    multiscaleGenomeTopologyReported : Bool
    multiscaleGenomeTopologyReportedIsTrue :
      multiscaleGenomeTopologyReported ≡ true

    irreversibleMixingReported : Bool
    irreversibleMixingReportedIsTrue :
      irreversibleMixingReported ≡ true

    all406PairwiseAncestralFusionsSampledReported : Bool
    all406PairwiseAncestralFusionsSampledReportedIsTrue :
      all406PairwiseAncestralFusionsSampledReported ≡ true

    schematicDirectedReachabilityWitnessConstructed : Bool
    schematicDirectedReachabilityWitnessConstructedIsTrue :
      schematicDirectedReachabilityWitnessConstructed ≡ true

    chromosomeCountAloneDeterminesArchitectureHistory : Bool
    chromosomeCountAloneDeterminesArchitectureHistoryIsFalse :
      chromosomeCountAloneDeterminesArchitectureHistory ≡ false

    evolutionaryHighwaysMeanFutureEvolutionIsDeterministic : Bool
    evolutionaryHighwaysMeanFutureEvolutionIsDeterministicIsFalse :
      evolutionaryHighwaysMeanFutureEvolutionIsDeterministic ≡ false

    everyRealChromosomeRearrangementProvedIrreversible : Bool
    everyRealChromosomeRearrangementProvedIrreversibleIsFalse :
      everyRealChromosomeRearrangementProvedIrreversible ≡ false

    paperManifoldReimplementedInDASHI : Bool
    paperManifoldReimplementedInDASHIIsFalse :
      paperManifoldReimplementedInDASHI ≡ false

open SourceClaimScope public

canonicalSourceClaimScope : SourceClaimScope
canonicalSourceClaimScope =
  sourceClaimScope
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
