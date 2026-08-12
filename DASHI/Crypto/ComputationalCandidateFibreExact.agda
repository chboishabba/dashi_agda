module DASHI.Crypto.ComputationalCandidateFibreExact where

------------------------------------------------------------------------
-- EXACT PREIMAGE FIBRE != COMPUTATIONAL / EPISTEMIC CANDIDATE FIBRE
--
-- This corrects an important cryptographic over-reading of the quotient idiom.
-- LWE/MLWE security does not require the public-key map to be mathematically
-- many-to-one over the intended secret distribution.  Even an injective public
-- map can be difficult to invert under a resource-bounded computational model.
--
-- Reference / motivation:
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005. DOI: 10.1145/1060590.1060603.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

record PublicMap : Set₁ where
  constructor publicMap
  field
    Hidden Public : Set
    publish : Hidden → Public

open PublicMap public

ExactFibre : (system : PublicMap) → Public system → Hidden system → Set
ExactFibre system public hidden = publish system hidden ≡ public

record InjectivePublicMap (system : PublicMap) : Set₁ where
  constructor injectivePublicMap
  field
    injective : ∀ {left right} →
      publish system left ≡ publish system right → left ≡ right

open InjectivePublicMap public

injectiveFibreHasUniqueCandidate :
  ∀ {system : PublicMap}
    (oneToOne : InjectivePublicMap system)
    {hidden candidate : Hidden system} →
  ExactFibre system (publish system hidden) candidate →
  candidate ≡ hidden
injectiveFibreHasUniqueCandidate oneToOne match = injective oneToOne match

------------------------------------------------------------------------
-- Resource-bounded candidate fibre.
--
-- A verifier may admit a larger set of plausible states than the exact
-- preimage fibre.  This is the correct place for residual smallness tests.
------------------------------------------------------------------------

record CandidateFibreSystem : Set₁ where
  constructor candidateFibreSystem
  field
    Hidden Public : Set
    publish : Hidden → Public
    Plausible : Public → Hidden → Set
    trueStatePlausible : ∀ hidden → Plausible (publish hidden) hidden

open CandidateFibreSystem public

record CandidateFalsePositive
    (system : CandidateFibreSystem) : Set where
  constructor candidateFalsePositive
  field
    actual candidate : Hidden system
    candidatePlausible : Plausible system (publish system actual) candidate
    notExactPreimage : publish system candidate ≡ publish system actual → ⊥

open CandidateFalsePositive public

------------------------------------------------------------------------
-- Computational inversion is an extra object even when exact fibres are
-- singletons.  No function is manufactured from injectivity alone.
------------------------------------------------------------------------

record PublicInverter (system : PublicMap) : Set₁ where
  constructor publicInverter
  field
    invert : Public system → Hidden system
    inverseOnImage : ∀ hidden → invert (publish system hidden) ≡ hidden

open PublicInverter public

record ModelRelativeInversionCost (system : PublicMap) : Set₁ where
  constructor modelRelativeInversionCost
  field
    Model : Set
    cost : Model → Public system → Nat

open ModelRelativeInversionCost public

record ComputationalFibreBoundary : Set where
  constructor computationalFibreBoundary
  field
    injectiveImpliesEfficientInverse : Agda.Builtin.Bool.Bool
    injectiveImpliesEfficientInverseIsFalse : injectiveImpliesEfficientInverse ≡ Agda.Builtin.Bool.false
    plausibleCandidateMeansExactPreimage : Agda.Builtin.Bool.Bool
    plausibleCandidateMeansExactPreimageIsFalse : plausibleCandidateMeansExactPreimage ≡ Agda.Builtin.Bool.false

open import Agda.Builtin.Bool using (Bool; false)
open ComputationalFibreBoundary public

canonicalComputationalFibreBoundary : ComputationalFibreBoundary
canonicalComputationalFibreBoundary = computationalFibreBoundary false refl false refl
