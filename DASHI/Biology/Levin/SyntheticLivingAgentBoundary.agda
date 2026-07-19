module DASHI.Biology.Levin.SyntheticLivingAgentBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Novel multicellular constructs may realise behaviours absent from their
-- ordinary developmental history.  This does not by itself establish that
-- the behaviour was selected for, represented in the genome, conscious, or
-- ethically negligible.

record SyntheticLivingAgentBoundary : Set where
  field
    evolvedMaterial : Bool
    novelAssembly : Bool
    genomeUnmodified : Bool
    behaviourOutsideOrdinaryBodyPlan : Bool
    autonomousCoordinationWitnessed : Bool
    evolutionaryHistoryUnderdeterminesBehaviour : Bool
    noveltyNotAbsenceOfMechanism : Bool
    noveltyNotConsciousness : Bool
    noveltyNotNoMoralStatus : Bool
    candidateOnly : Bool
    reading : String

open SyntheticLivingAgentBoundary public

canonicalSyntheticLivingAgentBoundary : SyntheticLivingAgentBoundary
canonicalSyntheticLivingAgentBoundary = record
  { evolvedMaterial = true
  ; novelAssembly = true
  ; genomeUnmodified = true
  ; behaviourOutsideOrdinaryBodyPlan = true
  ; autonomousCoordinationWitnessed = true
  ; evolutionaryHistoryUnderdeterminesBehaviour = true
  ; noveltyNotAbsenceOfMechanism = false
  ; noveltyNotConsciousness = false
  ; noveltyNotNoMoralStatus = false
  ; candidateOnly = true
  ; reading =
      "Xenobot- and anthrobot-style constructs witness that evolved cellular material can support coordinated behaviours in novel assemblies; selection history and genome do not uniquely determine realised behaviour, but mechanism, consciousness, and moral status remain separate questions"
  }

canonicalNoveltyNotConsciousness :
  noveltyNotConsciousness canonicalSyntheticLivingAgentBoundary ≡ false
canonicalNoveltyNotConsciousness = refl
