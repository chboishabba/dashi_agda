module DASHI.Environment.LatentDepthFormalism where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_+_; _≤_)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Geometry.SSP369Ultrametric as Geo

------------------------------------------------------------------------
-- Scope
--
-- This module records the finite, checkable spine of the continuous-depth
-- formalism used by LES-style latent models.  It deliberately does not claim
-- that Agda's finite carrier is the real-number embedding itself.  Instead it
-- proves the exact prefix/depth bridge and types the boundary at which a
-- continuous or learned envelope must provide external numerical evidence.

Effect : Set
Effect = SSP.SSPTrit

DepthState : Nat → Set
DepthState = Vec Effect

tritDigit369 : Effect → Geo.Digit369
tritDigit369 SSP.sspNegOne = Geo.digit3
tritDigit369 SSP.sspZero = Geo.digit6
tritDigit369 SSP.sspPosOne = Geo.digit9

addressOf : ∀ {d : Nat} → DepthState d → Geo.Address d
addressOf [] = []
addressOf (x ∷ xs) = tritDigit369 x ∷ addressOf xs

agreementDepth : ∀ {d : Nat} → DepthState d → DepthState d → Nat
agreementDepth x y = Geo.agreementDepth (addressOf x) (addressOf y)

depthDistance : ∀ {d : Nat} → DepthState d → DepthState d → Nat
depthDistance x y = Geo.distance (addressOf x) (addressOf y)

selfAgreementIsDepth :
  ∀ {d : Nat} (x : DepthState d) →
  agreementDepth x x ≡ d
selfAgreementIsDepth x = Geo.agreementDepth-self (addressOf x)

selfDistanceIsZero :
  ∀ {d : Nat} (x : DepthState d) →
  depthDistance x x ≡ zero
selfDistanceIsZero x = Geo.distance-self-zero (addressOf x)

record CylinderWitness {d : Nat} (x y : DepthState d) : Set where
  constructor mkCylinderWitness
  field
    sharedDepth : Nat
    prefix : Geo.PrefixMatch sharedDepth (addressOf x) (addressOf y)
    sharedDepthSound : sharedDepth ≤ agreementDepth x y
open CylinderWitness public

canonicalCylinderWitness :
  ∀ {d : Nat} (x y : DepthState d) →
  CylinderWitness x y
canonicalCylinderWitness x y =
  mkCylinderWitness
    (agreementDepth x y)
    (Geo.prefixWitness (addressOf x) (addressOf y))
    (Geo.prefixMatch-sound (Geo.prefixWitness (addressOf x) (addressOf y)))

------------------------------------------------------------------------
-- Coarse-to-fine execution lanes.

-- Path A: deterministic screening and cheap invariant checks.
-- Path B: latent/surrogate exploration learned from authoritative runs.
-- Path C: finite mechanistic or otherwise authoritative analysis.
data ModelLane : Set where
  pathA-screening : ModelLane
  pathB-latent : ModelLane
  pathC-authoritative : ModelLane

nextLane : ModelLane → ModelLane
nextLane pathA-screening = pathB-latent
nextLane pathB-latent = pathC-authoritative
nextLane pathC-authoritative = pathC-authoritative

pathCIsFixed : nextLane pathC-authoritative ≡ pathC-authoritative
pathCIsFixed = refl

record EscalationEvidence : Set where
  constructor mkEscalationEvidence
  field
    outsideTrainingSupport : Bool
    residualTooLarge : Bool
    uncertaintyTooLarge : Bool
    conservationCheckFailed : Bool
    policyCritical : Bool
open EscalationEvidence public

anyEscalation : EscalationEvidence → Bool
anyEscalation e with outsideTrainingSupport e
... | true = true
... | false with residualTooLarge e
...   | true = true
...   | false with uncertaintyTooLarge e
...     | true = true
...     | false with conservationCheckFailed e
...       | true = true
...       | false = policyCritical e

chooseLane : ModelLane → EscalationEvidence → ModelLane
chooseLane lane evidence with anyEscalation evidence
... | true = nextLane lane
... | false = lane

noEscalationKeepsPathA :
  chooseLane pathA-screening
    (mkEscalationEvidence false false false false false)
  ≡ pathA-screening
noEscalationKeepsPathA = refl

policyCriticalEscalatesPathB :
  chooseLane pathB-latent
    (mkEscalationEvidence false false false false true)
  ≡ pathC-authoritative
policyCriticalEscalatesPathB = refl

------------------------------------------------------------------------
-- MDL-style finite model selection.

record ModelCost : Set where
  constructor mkModelCost
  field
    residualCost : Nat
    structureCost : Nat
    authorityInvocationCost : Nat
open ModelCost public

totalCost : ModelCost → Nat
totalCost c = residualCost c + structureCost c + authorityInvocationCost c

record Candidate (Carrier : Set) : Set where
  constructor mkCandidate
  field
    payload : Carrier
    lane : ModelLane
    activeDepth : Nat
    cost : ModelCost
open Candidate public

record MDLMinimum {Carrier : Set}
                  (chosen : Candidate Carrier)
                  (candidates : List (Candidate Carrier)) : Set where
  constructor mkMDLMinimum
  field
    noMoreExpensiveThan :
      ∀ candidate →
      candidate ∈ candidates →
      totalCost (cost chosen) ≤ totalCost (cost candidate)
open MDLMinimum public

------------------------------------------------------------------------
-- External continuous / learned envelope contract.

record EnvelopeContract : Set₁ where
  constructor mkEnvelopeContract
  field
    Latent : Set
    embedDepthState : ∀ {d : Nat} → DepthState d → Latent
    predictsFrom : Latent → Latent
    residualObservable : Latent → Effect

    -- Evidence supplied by the numerical or statistical implementation.
    -- These are fields rather than claimed theorems here.
    depthWeighted : Set
    firstDifferenceControlsDistance : Set
    injectiveInDeclaredRegime : Set
    trainingSupportSpecified : Set
    uncertaintyCalibrated : Set
open EnvelopeContract public

record LatentDepthStatus : Set where
  constructor mkLatentDepthStatus
  field
    exactFiniteTritCarrier : Bool
    exactPrefixGeometry : Bool
    continuousEnvelopeIsBoundaryContract : Bool
    learnedModelIsNotAuthorityByItself : Bool
    pathCEscalationAvailable : Bool
open LatentDepthStatus public

canonicalLatentDepthStatus : LatentDepthStatus
canonicalLatentDepthStatus =
  mkLatentDepthStatus true true true true true

latentDepthSummary : String
latentDepthSummary =
  "Finite SSP trit streams inherit the checked 369 prefix ultrametric; learned/continuous envelopes remain evidence-bearing boundary contracts; execution escalates A -> B -> C when support, residual, uncertainty, conservation, or policy gates require it."
