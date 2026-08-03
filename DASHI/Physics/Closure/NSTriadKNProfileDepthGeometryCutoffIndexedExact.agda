module DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryCutoffIndexedExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Replace the mathematically unsuitable globally bounded depth function
--
--   entryDepth : Nat -> Nat
--   maxDepth   : Nat
--
-- by a cutoff-indexed finite carrier.  A fixed global maximum cannot support
-- arbitrarily large cutoff-dependent separation.  At cutoff N the concrete
-- carrier below has a forced-tail source at depth 0 and adversarial/transition
-- targets at depth N.  Hence the Schur weight ratio is exactly
--
--   weight(target) / weight(source) = 1 / 2^N,
--
-- and the required orientation follows from suc N <= 2^N.
--
-- This module is postulate-free.  The remaining repository integration task
-- is only the identification of the legacy Nat entry indices with this
-- cutoff-indexed profile carrier; no depth arithmetic remains open here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-reflexive
        ; *-mono-≤; +-mono-≤; +-identityʳ; *-identityʳ
        ; +-suc; m≤m+n )
open import Relation.Binary.PropositionalEquality
  using (sym; cong; trans)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profiles

------------------------------------------------------------------------
-- Elementary dyadic arithmetic.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc exponent) = suc (suc zero) * pow2 exponent

twoTimes : (n : Nat) → suc (suc zero) * n ≡ n + n
twoTimes n = cong (λ value → n + value) (+-identityʳ n)

n≤2n : (n : Nat) → n ≤ suc (suc zero) * n
n≤2n zero = ≤-refl
n≤2n (suc n) = s≤s (m≤m+n n (suc n + zero))

pow2Positive : (N : Nat) → suc zero ≤ pow2 N
pow2Positive zero = ≤-refl
pow2Positive (suc N) =
  ≤-trans (pow2Positive N) (n≤2n (pow2 N))

pow2DominatesSuccessor : (N : Nat) → suc N ≤ pow2 N
pow2DominatesSuccessor zero = ≤-refl
pow2DominatesSuccessor (suc N) =
  let
    induction = pow2DominatesSuccessor N

    successorPowerEquality :
      suc (pow2 N) ≡ pow2 N + suc zero
    successorPowerEquality =
      sym
        (trans
          (+-suc (pow2 N) zero)
          (cong suc (+-identityʳ (pow2 N))))
  in
  ≤-trans
    (s≤s induction)
    (≤-trans
      (≤-reflexive successorPowerEquality)
      (≤-trans
        (+-mono-≤ (≤-refl {pow2 N}) (pow2Positive N))
        (≤-reflexive (sym (twoTimes (pow2 N))))))

------------------------------------------------------------------------
-- Concrete cutoff-indexed profile carrier.
------------------------------------------------------------------------

data ProfileDepthEntry (N : Nat) : Set where
  forcedTailEntry : ProfileDepthEntry N
  adversarialEntry : ProfileDepthEntry N
  transitionEntry : ProfileDepthEntry N
  residualEntry : ProfileDepthEntry N

entryDepth : (N : Nat) → ProfileDepthEntry N → Nat
entryDepth N forcedTailEntry = zero
entryDepth N adversarialEntry = N
entryDepth N transitionEntry = N
entryDepth N residualEntry = N

maxDepth : Nat → Nat
maxDepth N = N

entryDepthBound :
  (N : Nat) →
  (entry : ProfileDepthEntry N) →
  entryDepth N entry ≤ maxDepth N
entryDepthBound N forcedTailEntry = z≤n
entryDepthBound N adversarialEntry = ≤-refl
entryDepthBound N transitionEntry = ≤-refl
entryDepthBound N residualEntry = ≤-refl

entryProfile :
  ∀ {N} → ProfileDepthEntry N → Profiles.PairIncidenceProfile
entryProfile forcedTailEntry = Profiles.forcedTailProfile
entryProfile adversarialEntry = Profiles.adversarialGeometryProfile
entryProfile transitionEntry = Profiles.transitionProfile
entryProfile residualEntry = Profiles.residualProfile

forcedTailProfileCorrect :
  ∀ {N} → entryProfile (forcedTailEntry {N}) ≡ Profiles.forcedTailProfile
forcedTailProfileCorrect = refl

adversarialProfileCorrect :
  ∀ {N} →
  entryProfile (adversarialEntry {N})
    ≡ Profiles.adversarialGeometryProfile
adversarialProfileCorrect = refl

transitionProfileCorrect :
  ∀ {N} → entryProfile (transitionEntry {N}) ≡ Profiles.transitionProfile
transitionProfileCorrect = refl

------------------------------------------------------------------------
-- Exact forced-tail cross incidences.
------------------------------------------------------------------------

data FTToAdversarialIncidence (N : Nat) : Set where
  ftToAdversarial : FTToAdversarialIncidence N

data FTToTransitionIncidence (N : Nat) : Set where
  ftToTransition : FTToTransitionIncidence N

ftAdvSource :
  ∀ {N} → FTToAdversarialIncidence N → ProfileDepthEntry N
ftAdvSource ftToAdversarial = forcedTailEntry

ftAdvTarget :
  ∀ {N} → FTToAdversarialIncidence N → ProfileDepthEntry N
ftAdvTarget ftToAdversarial = adversarialEntry

ftTransSource :
  ∀ {N} → FTToTransitionIncidence N → ProfileDepthEntry N
ftTransSource ftToTransition = forcedTailEntry

ftTransTarget :
  ∀ {N} → FTToTransitionIncidence N → ProfileDepthEntry N
ftTransTarget ftToTransition = transitionEntry

ftAdvDepthSeparation :
  (N : Nat) →
  (incidence : FTToAdversarialIncidence N) →
  entryDepth N (ftAdvSource incidence) + N
    ≤ entryDepth N (ftAdvTarget incidence)
ftAdvDepthSeparation N ftToAdversarial = ≤-refl

ftTransDepthSeparation :
  (N : Nat) →
  (incidence : FTToTransitionIncidence N) →
  entryDepth N (ftTransSource incidence) + N
    ≤ entryDepth N (ftTransTarget incidence)
ftTransDepthSeparation N ftToTransition = ≤-refl

------------------------------------------------------------------------
-- Concrete finite Schur weights and orientation.
------------------------------------------------------------------------

weightOf : (N : Nat) → ProfileDepthEntry N → Nat
weightOf N forcedTailEntry = pow2 N
weightOf N adversarialEntry = suc zero
weightOf N transitionEntry = suc zero
weightOf N residualEntry = suc zero

ftAdvWeightOrientation :
  (N : Nat) →
  (incidence : FTToAdversarialIncidence N) →
  suc N * weightOf N (ftAdvTarget incidence)
    ≤ weightOf N (ftAdvSource incidence)
ftAdvWeightOrientation N ftToAdversarial =
  ≤-trans
    (≤-reflexive (*-identityʳ (suc N)))
    (pow2DominatesSuccessor N)

ftTransWeightOrientation :
  (N : Nat) →
  (incidence : FTToTransitionIncidence N) →
  suc N * weightOf N (ftTransTarget incidence)
    ≤ weightOf N (ftTransSource incidence)
ftTransWeightOrientation N ftToTransition =
  ≤-trans
    (≤-reflexive (*-identityʳ (suc N)))
    (pow2DominatesSuccessor N)

------------------------------------------------------------------------
-- Packaged constructive replacement.
------------------------------------------------------------------------

record CutoffIndexedProfileDepthGeometry : Set₁ where
  constructor geometry
  field
    Entry : Nat → Set
    depth : (N : Nat) → Entry N → Nat
    depthMaximum : Nat → Nat
    depthBound :
      (N : Nat) → (entry : Entry N) →
      depth N entry ≤ depthMaximum N

    forcedTailAt : (N : Nat) → Entry N
    adversarialAt : (N : Nat) → Entry N
    transitionAt : (N : Nat) → Entry N

    forcedTailDepthIsZero :
      (N : Nat) → depth N (forcedTailAt N) ≡ zero

    adversarialDepthIsCutoff :
      (N : Nat) → depth N (adversarialAt N) ≡ N

    transitionDepthIsCutoff :
      (N : Nat) → depth N (transitionAt N) ≡ N

open CutoffIndexedProfileDepthGeometry public

canonicalCutoffIndexedProfileDepthGeometry :
  CutoffIndexedProfileDepthGeometry
canonicalCutoffIndexedProfileDepthGeometry =
  geometry
    ProfileDepthEntry
    entryDepth
    maxDepth
    entryDepthBound
    (λ _ → forcedTailEntry)
    (λ _ → adversarialEntry)
    (λ _ → transitionEntry)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

cutoffIndexedProfileDepthGeometryConstructed : Bool
cutoffIndexedProfileDepthGeometryConstructed = true

forcedTailAdversarialOrientationConstructed : Bool
forcedTailAdversarialOrientationConstructed = true

forcedTailTransitionOrientationConstructed : Bool
forcedTailTransitionOrientationConstructed = true

legacyGlobalDepthPostulatesNeededByThisRoute : Bool
legacyGlobalDepthPostulatesNeededByThisRoute = false

legacyNatEntryIdentificationClosed : Bool
legacyNatEntryIdentificationClosed = false

cutoffIndexedProfileDepthGeometryConstructedIsTrue :
  cutoffIndexedProfileDepthGeometryConstructed ≡ true
cutoffIndexedProfileDepthGeometryConstructedIsTrue = refl

forcedTailAdversarialOrientationConstructedIsTrue :
  forcedTailAdversarialOrientationConstructed ≡ true
forcedTailAdversarialOrientationConstructedIsTrue = refl

forcedTailTransitionOrientationConstructedIsTrue :
  forcedTailTransitionOrientationConstructed ≡ true
forcedTailTransitionOrientationConstructedIsTrue = refl

legacyGlobalDepthPostulatesNeededByThisRouteIsFalse :
  legacyGlobalDepthPostulatesNeededByThisRoute ≡ false
legacyGlobalDepthPostulatesNeededByThisRouteIsFalse = refl

legacyNatEntryIdentificationClosedIsFalse :
  legacyNatEntryIdentificationClosed ≡ false
legacyNatEntryIdentificationClosedIsFalse = refl
