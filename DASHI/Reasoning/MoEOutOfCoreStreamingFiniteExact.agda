module DASHI.Reasoning.MoEOutOfCoreStreamingFiniteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Finite, source-independent SPECIMENS, not a Qwen/Swiftlet/oLLM
-- kernel-refinement claim. Only a correct selected expert is decoded.
------------------------------------------------------------------------

data Expert : Set where
  firstExpert : Expert
  secondExpert : Expert

data Revision : Set where
  oldRevision : Revision
  newRevision : Revision

route : Bool → Expert
route false = firstExpert
route true  = secondExpert

decode : Expert → Nat
decode firstExpert  = 3
decode secondExpert = 5

-- Model-side source of truth. A demand-loaded cache returns the
-- corresponding selected weight; its eviction choice is unobservable
-- PROVIDED fetched values and revisions agree with the source.
readStoredExpert : Expert → Nat
readStoredExpert firstExpert  = 3
readStoredExpert secondExpert = 5

demandFetch : Expert → Nat
demandFetch = readStoredExpert

selectedFetchMatchesDenseReference :
  (e : Expert) → demandFetch e ≡ decode e
selectedFetchMatchesDenseReference firstExpert  = refl
selectedFetchMatchesDenseReference secondExpert = refl

streamedSelectionMatchesDenseReference :
  (b : Bool) → demandFetch (route b) ≡ decode (route b)
streamedSelectionMatchesDenseReference false = refl
streamedSelectionMatchesDenseReference true  = refl

-- One selected expert rather than the entire two-expert collection
-- is enough to evaluate this specific finite specimen.
selectedCount : Nat
selectedCount = 1

totalCount : Nat
totalCount = 2

selectedCountNoGreaterThanTotal :
  selectedCount ≤ totalCount
selectedCountNoGreaterThanTotal = s≤s (s≤s z≤n)

-- A changed source revision can reuse the same expert identifier with a
-- different weight. Identity-only caches are therefore insufficient.
revisionedWeight : Revision → Expert → Nat
revisionedWeight oldRevision firstExpert  = 3
revisionedWeight newRevision firstExpert  = 4
revisionedWeight _ secondExpert = 5

sameExpertIdAcrossRevisions : Expert ≡ Expert
sameExpertIdAcrossRevisions = refl

staleExpertWeightDiffers :
  revisionedWeight oldRevision firstExpert ≡
  revisionedWeight newRevision firstExpert → ⊥
staleExpertWeightDiffers ()

-- Steering before a discontinuous router need not equal a post-route
-- activation change; neither operation is assumed to be semantic steering.
flip : Bool → Bool
flip false = true
flip true  = false

preRouteSteer : Bool → Nat
preRouteSteer b = decode (route (flip b))

postRouteUnitShift : Bool → Nat
postRouteUnitShift b = suc (decode (route b))

preAndPostSteeringDiffer :
  preRouteSteer false ≡ postRouteUnitShift false → ⊥
preAndPostSteeringDiffer ()

-- Nondeduction firewall: the finite lemmas above show neither lower
-- wall-clock latency nor bounded SSD bytes, source-kernel correctness,
-- Qwen-specific fidelity, nor sound Sophontic semantic interpretation.
