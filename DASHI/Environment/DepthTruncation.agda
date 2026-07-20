module DASHI.Environment.DepthTruncation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_+_; _≤_; z≤n; s≤s)

import DASHI.Environment.LatentDepthFormalism as Latent

EffectStream : Set
EffectStream = List Latent.Effect

truncate : Nat → EffectStream → EffectStream
truncate zero xs = []
truncate (suc k) [] = []
truncate (suc k) (x ∷ xs) = x ∷ truncate k xs

data Prefix : EffectStream → EffectStream → Set where
  prefix-empty : ∀ {ys} → Prefix [] ys
  prefix-cons :
    ∀ {x xs ys} →
    Prefix xs ys →
    Prefix (x ∷ xs) (x ∷ ys)

truncateIsPrefix : ∀ k xs → Prefix (truncate k xs) xs
truncateIsPrefix zero xs = prefix-empty
truncateIsPrefix (suc k) [] = prefix-empty
truncateIsPrefix (suc k) (x ∷ xs) = prefix-cons (truncateIsPrefix k xs)

truncate-idempotent : ∀ k xs → truncate k (truncate k xs) ≡ truncate k xs
truncate-idempotent zero xs = refl
truncate-idempotent (suc k) [] = refl
truncate-idempotent (suc k) (x ∷ xs) rewrite truncate-idempotent k xs = refl

shallowerPrefixOfDeeper :
  ∀ k n xs →
  Prefix (truncate k xs) (truncate (k + n) xs)
shallowerPrefixOfDeeper zero n xs = prefix-empty
shallowerPrefixOfDeeper (suc k) n [] = prefix-empty
shallowerPrefixOfDeeper (suc k) n (x ∷ xs) =
  prefix-cons (shallowerPrefixOfDeeper k n xs)

record CylinderAt (k : Nat) (centre candidate : EffectStream) : Set where
  constructor mkCylinderAt
  field
    sameTruncation : truncate k centre ≡ truncate k candidate
open CylinderAt public

selfInCylinder : ∀ k xs → CylinderAt k xs xs
selfInCylinder k xs = mkCylinderAt refl

prefixAgreementGivesCylinder :
  ∀ {k : Nat} {centre candidate : EffectStream} →
  truncate k centre ≡ truncate k candidate →
  CylinderAt k centre candidate
prefixAgreementGivesCylinder eq = mkCylinderAt eq

record DepthRefinement (shallow deep : Nat) : Set where
  constructor mkDepthRefinement
  field
    shallow≤deep : shallow ≤ deep
open DepthRefinement public

canonicalRefinement : ∀ k n → DepthRefinement k (k + n)
canonicalRefinement zero n = mkDepthRefinement z≤n
canonicalRefinement (suc k) n with canonicalRefinement k n
... | mkDepthRefinement p = mkDepthRefinement (s≤s p)

record ResidualDepthDecision : Set where
  constructor mkResidualDepthDecision
  field
    currentDepth : Nat
    proposedDepth : Nat
    residualImproves : Bool
    complexityBudgetAllows : Bool
    policyOrConservationForcesAuthority : Bool
    refinementWitness : DepthRefinement currentDepth proposedDepth
    deeperAnalysisIsCandidateNotMandate : Bool
open ResidualDepthDecision public

canonicalNoMandateBoundary :
  ∀ {k n : Nat} →
  ResidualDepthDecision
canonicalNoMandateBoundary {k} {n} =
  mkResidualDepthDecision
    k
    (k + n)
    true
    true
    false
    (canonicalRefinement k n)
    true
