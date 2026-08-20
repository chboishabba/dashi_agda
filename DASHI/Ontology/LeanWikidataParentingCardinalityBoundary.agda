module DASHI.Ontology.LeanWikidataParentingCardinalityBoundary where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge using (LeanTheoremContract)
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge
open import DASHI.Ontology.ProgenitorParentHyperfabric

------------------------------------------------------------------------
-- JMD proves a cardinality cap under his validated genetic-slot profile:
--
--   geneticSlotsTyped = true
--   singleGeneticParents = true
--   --------------------------------
--   card geneticParentsF <= 2
--
-- This does not entail that a generation has exactly two progenitors, exactly
-- two genetic contributors, or even that both P22/P25 slots are populated.
------------------------------------------------------------------------

data AtMostTwo : Nat → Set where
  atMostZero : AtMostTwo zero
  atMostOne : AtMostTwo (suc zero)
  atMostTwo : AtMostTwo (suc (suc zero))

oneGeneticContributorGeneration : GenerationEvent
oneGeneticContributorGeneration =
  generationEvent
    "single recorded genetic contributor"
    individualLevel
    (progenitorContribution "one contributor" nuclear ∷ [])
    unrestrictedProfile

oneContributorCount :
  progenitorCount oneGeneticContributorGeneration ≡ suc zero
oneContributorCount = refl

oneContributorSatisfiesCap :
  AtMostTwo (progenitorCount oneGeneticContributorGeneration)
oneContributorSatisfiesCap = atMostOne

-- Empty and singleton fibres witness that an upper bound alone cannot recover
-- exact-two cardinality.
record JMDGeneticCardinalityBoundary : Set where
  constructor jmdGeneticCardinalityBoundary
  field
    importedCapContract : LeanTheoremContract
    capMeansExactlyTwo : Bool
    capDeterminesReproductiveProfile : Bool
open JMDGeneticCardinalityBoundary public

canonicalJMDGeneticCardinalityBoundary : JMDGeneticCardinalityBoundary
canonicalJMDGeneticCardinalityBoundary =
  jmdGeneticCardinalityBoundary
    jmdGeneticBoundUnderTwoSlotProfile
    false
    false

jmdCapDoesNotMeanExactlyTwo :
  capMeansExactlyTwo canonicalJMDGeneticCardinalityBoundary ≡ false
jmdCapDoesNotMeanExactlyTwo = refl

jmdCapDoesNotDetermineReproductiveProfile :
  capDeterminesReproductiveProfile canonicalJMDGeneticCardinalityBoundary ≡ false
jmdCapDoesNotDetermineReproductiveProfile = refl

-- DASHI's exact-two theorem remains explicitly hypothesis-indexed.
exactTwoStillRequiresBiparentalWitness :
  (event : GenerationEvent) →
  BiparentalNuclearWitness event →
  progenitorCount event ≡ suc (suc zero)
exactTwoStillRequiresBiparentalWitness = binaryBoundRequiresBiparentalProfile
