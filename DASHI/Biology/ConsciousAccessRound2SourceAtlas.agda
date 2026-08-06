module DASHI.Biology.ConsciousAccessRound2SourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attributed source atlas for the round-two mathematical bridges.

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    importedRole : String
    excludedPromotion : String

open SourceRecord public

petriHomologySource : SourceRecord
petriHomologySource =
  sourceRecord
    "Giovanni Petri; Paul Expert; Federico Turkheimer; Robin Carhart-Harris; David Nutt; Peter Hellyer; Francesco Vaccarino"
    "Homological scaffolds of brain functional networks"
    "Journal of the Royal Society Interface"
    2014
    "10.1098/rsif.2014.0873"
    "Motivates higher-order relational structure beyond pairwise edge lists."
    "Persistent or homological structure is not identified by itself with consciousness."

hutchisonDynamicConnectivitySource : SourceRecord
hutchisonDynamicConnectivitySource =
  sourceRecord
    "R. Matthew Hutchison et al."
    "Dynamic functional connectivity: Promise, issues, and interpretations"
    "NeuroImage"
    2013
    "10.1016/j.neuroimage.2013.05.079"
    "Motivates time- and state-indexed functional connectivity over fixed anatomy."
    "A changing proxy graph is not promoted to direct neural mechanism or mind reading."

decoDynamicBrainSource : SourceRecord
decoDynamicBrainSource =
  sourceRecord
    "Gustavo Deco; Viktor Jirsa; Peter A. Robinson; Michael Breakspear; Karl Friston"
    "The Dynamic Brain: From Spiking Neurons to Neural Masses and Cortical Fields"
    "PLoS Computational Biology"
    2008
    "10.1371/journal.pcbi.0040100"
    "Motivates multiscale dynamical carriers linking local neural state and large-scale fields."
    "The finite DASHI model is not claimed to instantiate a biologically calibrated neural mass model."

kelsoMetastabilitySource : SourceRecord
kelsoMetastabilitySource =
  sourceRecord
    "J. A. Scott Kelso"
    "Multistability and metastability: understanding dynamic coordination in the brain"
    "Philosophical Transactions of the Royal Society B"
    2012
    "10.1098/rstb.2011.0351"
    "Motivates recurrently viable but escapable coordination regimes."
    "Metastability is not treated as a sufficient marker of phenomenal consciousness."

canonicalRound2Sources : List SourceRecord
canonicalRound2Sources =
  petriHomologySource
  ∷ hutchisonDynamicConnectivitySource
  ∷ decoDynamicBrainSource
  ∷ kelsoMetastabilitySource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalRound2SourceCount : Nat
canonicalRound2SourceCount = listCount canonicalRound2Sources

canonicalRound2SourceCountIsFour : canonicalRound2SourceCount ≡ 4
canonicalRound2SourceCountIsFour = refl
