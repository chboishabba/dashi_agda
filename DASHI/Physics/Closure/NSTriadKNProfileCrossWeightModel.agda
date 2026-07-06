module DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero; _*_; _+_)
open import Data.Nat using (_≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; *-mono-≤; +-assoc; *-assoc; *-comm;
         +-identityʳ; *-identityʳ; +-suc; m≤m+n; ∸-monoʳ-≤)
open import Relation.Binary.PropositionalEquality using (sym; cong; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase

-----------------------------------------------------------------------
-- Shell depth model.
--
-- Each entry index k : Nat has an associated shell depth d(k) : Nat,
-- bounded by the global maximum depth maxDepth.
--
-- weightOf k = 2^{maxDepth − d(k)}
--
-- Coarsest entries (depth 0) receive weight 2^{maxDepth}.
-- Finest entries (depth maxDepth) receive weight 1.
-----------------------------------------------------------------------

entryDepth : Nat → Nat
entryDepth = DepthBase.entryDepth

maxDepth : Nat
maxDepth = DepthBase.maxDepth

entryDepthBound : (k : Nat) → entryDepth k ≤ maxDepth
entryDepthBound = DepthBase.entryDepthBound

pow2 : Nat → Nat
pow2 zero    = 1
pow2 (suc m) = 2 * pow2 m

weightOf : Nat → Nat
weightOf k = pow2 (maxDepth ∸ entryDepth k)

-----------------------------------------------------------------------
-- 2 * n ≡ n + n  (definitional expansion)
-----------------------------------------------------------------------

2*n≡n+n : (n : Nat) → 2 * n ≡ n + n
2*n≡n+n n = cong (λ X → n + X) (+-identityʳ n)

-----------------------------------------------------------------------
-- pow2 (a + b) ≡ pow2 a * pow2 b
-----------------------------------------------------------------------

pow2-homo : (a b : Nat) → pow2 (a + b) ≡ pow2 a * pow2 b
pow2-homo a zero    = trans (cong pow2 (+-identityʳ a)) (sym (*-identityʳ (pow2 a)))
pow2-homo a (suc b) = 
  let
    IH   = pow2-homo a b
    -- pow2 (a + suc b) ≡ pow2 (suc (a + b))
    eq1 : pow2 (a + suc b) ≡ pow2 (suc (a + b))
    eq1 = cong pow2 (+-suc a b)
    -- pow2 (suc (a + b)) = 2 * pow2 (a + b)
    eq2 : pow2 (suc (a + b)) ≡ 2 * pow2 (a + b)
    eq2 = refl  -- definitional: pow2 (suc _) = 2 * pow2 _
    -- 2 * pow2 (a + b) ≡ 2 * (pow2 a * pow2 b)
    eq3 : 2 * pow2 (a + b) ≡ 2 * (pow2 a * pow2 b)
    eq3 = cong (λ X → 2 * X) IH
    -- 2 * (pow2 a * pow2 b) ≡ pow2 a * (2 * pow2 b)
    eq4 : 2 * (pow2 a * pow2 b) ≡ pow2 a * (2 * pow2 b)
    eq4 = trans (sym (*-assoc 2 (pow2 a) (pow2 b)))
                (trans (cong (λ X → X * pow2 b) (*-comm 2 (pow2 a)))
                       (*-assoc (pow2 a) 2 (pow2 b)))
    -- pow2 a * (2 * pow2 b) ≡ pow2 a * pow2 (suc b)
    eq5 : pow2 a * (2 * pow2 b) ≡ pow2 a * pow2 (suc b)
    eq5 = refl  -- definitional: pow2 (suc b) = 2 * pow2 b
  in
    trans eq1 (trans eq2 (trans eq3 (trans eq4 eq5)))

-----------------------------------------------------------------------
-- n ≤ 2 * n
-----------------------------------------------------------------------

n≤2n : (n : Nat) → n ≤ 2 * n
n≤2n zero    = ≤-refl
n≤2n (suc n) = s≤s (m≤m+n n (suc n + 0))

-----------------------------------------------------------------------
-- 1 ≤ pow2 N for all N
-----------------------------------------------------------------------

pow2Pos : (N : Nat) → 1 ≤ pow2 N
pow2Pos zero    = ≤-refl
pow2Pos (suc N) = ≤-trans (pow2Pos N) (n≤2n (pow2 N))

-----------------------------------------------------------------------
-- a ≤ b → pow2 a ≤ pow2 b
-----------------------------------------------------------------------

pow2-mono : {a b : Nat} → a ≤ b → pow2 a ≤ pow2 b
pow2-mono {b = b} z≤n = pow2Pos b      -- a = 0, pow2 0 = 1 ≤ pow2 b
pow2-mono (s≤s a≤b) = *-mono-≤ (≤-refl {2}) (pow2-mono a≤b)

-----------------------------------------------------------------------
-- suc N ≤ 2^N for all N  (by induction)
-----------------------------------------------------------------------

pow2GeqSucN : (N : Nat) → suc N ≤ pow2 N
pow2GeqSucN zero    = ≤-refl
pow2GeqSucN (suc N) =
  let
    IH = pow2GeqSucN N

    -- suc (pow2 N) ≡ pow2 N + 1
    suc-pow2N≡pow2N+1 : suc (pow2 N) ≡ pow2 N + 1
    suc-pow2N≡pow2N+1 =
      sym (trans (+-suc (pow2 N) 0) (cong suc (+-identityʳ (pow2 N))))
  in
  ≤-trans
    (s≤s IH)                                                     -- suc(suc N) ≤ suc(pow2 N)
    (≤-trans
      (≤-reflexive suc-pow2N≡pow2N+1)                              -- suc(pow2 N) ≤ pow2 N + 1
      (≤-trans
        (+-mono-≤ (≤-refl {pow2 N}) (pow2Pos N))                   -- pow2 N + 1 ≤ pow2 N + pow2 N
        (≤-reflexive (sym (2*n≡n+n (pow2 N))))))                   -- pow2 N + pow2 N = 2*pow2 N
                                                                    -- = pow2 (suc N)

-----------------------------------------------------------------------
-- m ≤ n → m + (n ∸ m) ≤ n
--
-- Key lemma for reasoning with truncated subtraction whose truncation
-- is inoperative because the ordering premise guarantees n ≥ m.
-----------------------------------------------------------------------

m+[n∸m]≤n : {m n : Nat} → m ≤ n → m + (n ∸ m) ≤ n
m+[n∸m]≤n z≤n       = ≤-refl
m+[n∸m]≤n (s≤s m≤n) = s≤s (m+[n∸m]≤n m≤n)

-----------------------------------------------------------------------
-- a + b ≤ c → b ≤ c ∸ a
--
-- Shifts a term across truncated subtraction when the total sum is
-- bounded.  Proved by induction on a with case analysis on c.
-----------------------------------------------------------------------

m+n≤p→n≤p∸m : (a b c : Nat) → a + b ≤ c → b ≤ c ∸ a
m+n≤p→n≤p∸m zero    b c prf = prf
m+n≤p→n≤p∸m (suc a) b zero    ()
m+n≤p→n≤p∸m (suc a) b (suc c) (s≤s prf) = m+n≤p→n≤p∸m a b c prf

-----------------------------------------------------------------------
-- Depth weight separation lemma.
--
-- If d(j) ≥ d(i) + k and both depths are bounded by maxDepth, then
-- 2^{k} · w(j) ≤ w(i).
--
-- Let d_i = entryDepth i, d_j = entryDepth j, M = maxDepth.
-- From d_i + k ≤ d_j ≤ M, we have:
--
--   1. M ∸ d_j ≤ M ∸ (d_i + k)                  (∸-monoʳ-≤ on di+k≤dj)
--   2. pow2 (M ∸ d_j) ≤ pow2 (M ∸ (d_i + k))    (pow2-mono from 1)
--   3. pow2 k * pow2 (M ∸ d_j) ≤ pow2 k * pow2 (M ∸ (d_i + k))
--                                                 (*-mono-≤ on 2)
--   4. pow2 k * pow2 (M ∸ (d_i + k))
--      = pow2 (k + (M ∸ (d_i + k)))              (pow2-homo)
--
--   5. k + (M ∸ (d_i + k)) ≤ M ∸ d_i
--      because (d_i + k) + (M ∸ (d_i + k)) ≤ M   (m+[n∸m]≤n on di+k≤M)
--      then shift by m+n≤p→n≤p∸m with a = d_i.
--
--   6. pow2 (k + (M ∸ (d_i + k))) ≤ pow2 (M ∸ d_i)  (pow2-mono from 5)
--
-- Chain 1→2→3→4→6 gives pow2 k * weightOf j ≤ weightOf i.
-----------------------------------------------------------------------

depthWeightSeparation :
  (i j : Nat) (k : Nat) →
  entryDepth i ≤ maxDepth →
  entryDepth j ≤ maxDepth →
  entryDepth i + k ≤ entryDepth j →
  pow2 k * weightOf j ≤ weightOf i
depthWeightSeparation i j k di≤M dj≤M di+k≤dj =
  let
    M   = maxDepth
    d_i = entryDepth i
    d_j = entryDepth j

    di+k≤M : d_i + k ≤ M
    di+k≤M = ≤-trans di+k≤dj dj≤M

    -- 1. M ∸ d_j ≤ M ∸ (d_i + k)
    M-dj≤M-[di+k] : M ∸ d_j ≤ M ∸ (d_i + k)
    M-dj≤M-[di+k] = ∸-monoʳ-≤ M di+k≤dj

    -- 2. pow2 (M ∸ d_j) ≤ pow2 (M ∸ (d_i + k))
    p2Mdj≤p2M[di+k] : pow2 (M ∸ d_j) ≤ pow2 (M ∸ (d_i + k))
    p2Mdj≤p2M[di+k] = pow2-mono M-dj≤M-[di+k]

    -- 3. pow2 k * pow2 (M ∸ d_j) ≤ pow2 k * pow2 (M ∸ (d_i + k))
    step3 : pow2 k * pow2 (M ∸ d_j) ≤ pow2 k * pow2 (M ∸ (d_i + k))
    step3 = *-mono-≤ (≤-refl {pow2 k}) p2Mdj≤p2M[di+k]

    -- 4. pow2 k * pow2 (M ∸ (d_i + k)) = pow2 (k + (M ∸ (d_i + k)))
    step4-eq : pow2 k * pow2 (M ∸ (d_i + k)) ≡ pow2 (k + (M ∸ (d_i + k)))
    step4-eq = sym (pow2-homo k (M ∸ (d_i + k)))
    step4 : pow2 k * pow2 (M ∸ (d_i + k)) ≤ pow2 (k + (M ∸ (d_i + k)))
    step4 = ≤-reflexive step4-eq

    -- 5. k + (M ∸ (d_i + k)) ≤ M ∸ d_i
    chain-lemma : k + (M ∸ (d_i + k)) ≤ M ∸ d_i
    chain-lemma = m+n≤p→n≤p∸m d_i (k + (M ∸ (d_i + k))) M
      (≤-trans
        (≤-reflexive (sym (+-assoc d_i k (M ∸ (d_i + k)))))
        (m+[n∸m]≤n di+k≤M))

    -- 6. pow2 (k + (M ∸ (d_i + k))) ≤ pow2 (M ∸ d_i)
    step6 : pow2 (k + (M ∸ (d_i + k))) ≤ pow2 (M ∸ d_i)
    step6 = pow2-mono chain-lemma

  in
    ≤-trans step3                                              -- pow2 k * w(j) ≤ pow2 k * pow2 (M ∸ (d_i + k))
      (≤-trans step4                                           -- = pow2 (k + (M ∸ (d_i + k)))
               step6)                                          -- ≤ pow2 (M ∸ d_i) = w(i)

-----------------------------------------------------------------------
-- Explicit depth-geometry surfaces.
--
-- Blocker 1 is now isolated to profile-depth geometry, not arithmetic.
-- The missing data is therefore packaged as theorem-facing records:
--
--   1. an ordering witness d(i) ≤ d(j)
--   2. a logarithmic required-depth function
--   3. a profile-specific separation proof
--   4. a proof that the required depth yields suc N ≤ 2^k
--
-- The derived lemmas ftAdvDepthGainEnough / ftTransDepthGainEnough then
-- recover the old weak sufficient form without leaving the geometry
-- implicit.
-----------------------------------------------------------------------

record FTToAdversarialDepthGeometry : Set₁ where
  field
    logDepthRequired : Nat → Nat
    depthOrdering :
      (N i j : Nat) →
      Refinement.FTToAdversarialIncidence N i j →
      entryDepth i ≤ entryDepth j
    profileSeparation :
      (N i j : Nat) →
      Refinement.FTToAdversarialIncidence N i j →
      logDepthRequired N ≤ entryDepth j ∸ entryDepth i
    logDepthRequiredBound :
      (N : Nat) → suc N ≤ pow2 (logDepthRequired N)

record FTToTransitionDepthGeometry : Set₁ where
  field
    logDepthRequired : Nat → Nat
    depthOrdering :
      (N i j : Nat) →
      Refinement.FTToTransitionIncidence N i j →
      entryDepth i ≤ entryDepth j
    profileSeparation :
      (N i j : Nat) →
      Refinement.FTToTransitionIncidence N i j →
      logDepthRequired N ≤ entryDepth j ∸ entryDepth i
    logDepthRequiredBound :
      (N : Nat) → suc N ≤ pow2 (logDepthRequired N)

-----------------------------------------------------------------------
-- FT → adversarial geometry entry point.
--
-- First concrete attempt: take the required depth to be N itself.
-- Then the arithmetic field is discharged by pow2GeqSucN, and the only
-- remaining geometric input is the linear shell-separation theorem
--
--   entryDepth i + N ≤ entryDepth j.
--
-- If that turns out to be too strong, this is the exact place to replace
-- `advLogDepthRequired = N` by a weaker ceiling-log depth.
-----------------------------------------------------------------------

advLogDepthRequired : Nat → Nat
advLogDepthRequired = DepthBase.advLogDepthRequired

transLogDepthRequired : Nat → Nat
transLogDepthRequired = DepthBase.transLogDepthRequired

-----------------------------------------------------------------------
-- Profile-depth geometry surfaces.
--
-- The remaining Blocker 1 content is now expressed through explicit
-- profile/source/target depth data rather than opaque geometry records.
-- The intended route is:
--
--   FT→adv incidence   -> forced-tail source + adversarial target
--   FT→trans incidence -> forced-tail source + transition target
--   source upper bound + target lower bound -> linear depth separation
--
-- If the linear route turns out too strong, replace adv/trans
-- LogDepthRequired by a weaker ceiling-log function and keep the same
-- bridge shape.
-----------------------------------------------------------------------

ForcedTailSource : Nat → Nat → Set
ForcedTailSource = DepthBase.ForcedTailSource

AdversarialTarget : Nat → Nat → Set
AdversarialTarget = DepthBase.AdversarialTarget

TransitionTarget : Nat → Nat → Set
TransitionTarget = DepthBase.TransitionTarget

record ProfileDepthSemantics : Set₁ where
  field
    forcedTailSourceDepthUpper :
      (N i : Nat) →
      ForcedTailSource N i →
      entryDepth i ≤ DepthBase.forcedTailSourceDepthCap N

    adversarialTargetDepthLower :
      (N j : Nat) →
      AdversarialTarget N j →
      DepthBase.forcedTailSourceDepthCap N + advLogDepthRequired N ≤ entryDepth j

    transitionTargetDepthLower :
      (N j : Nat) →
      TransitionTarget N j →
      DepthBase.forcedTailSourceDepthCap N + transLogDepthRequired N ≤ entryDepth j

canonicalProfileDepthSemantics : ProfileDepthSemantics
canonicalProfileDepthSemantics = record
  { forcedTailSourceDepthUpper =
      λ N i ft →
        DepthBase.ForcedTailSourceDef.depthUpper ft
  ; adversarialTargetDepthLower =
      λ N j adv →
        DepthBase.AdversarialTargetDef.depthLower adv
  ; transitionTargetDepthLower =
      λ N j trans →
        DepthBase.TransitionTargetDef.depthLower trans
  }

forcedTailSourceDepthCap : Nat → Nat
forcedTailSourceDepthCap = DepthBase.forcedTailSourceDepthCap

forcedTailSourceDepthUpper :
  (N i : Nat) →
  ForcedTailSource N i →
  entryDepth i ≤ forcedTailSourceDepthCap N
forcedTailSourceDepthUpper =
  ProfileDepthSemantics.forcedTailSourceDepthUpper
    canonicalProfileDepthSemantics

adversarialTargetDepthLower :
  (N j : Nat) →
  AdversarialTarget N j →
  forcedTailSourceDepthCap N + advLogDepthRequired N ≤ entryDepth j
adversarialTargetDepthLower =
  ProfileDepthSemantics.adversarialTargetDepthLower
    canonicalProfileDepthSemantics

transitionTargetDepthLower :
  (N j : Nat) →
  TransitionTarget N j →
  forcedTailSourceDepthCap N + transLogDepthRequired N ≤ entryDepth j
transitionTargetDepthLower =
  ProfileDepthSemantics.transitionTargetDepthLower
    canonicalProfileDepthSemantics

ftAdvSource :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  ForcedTailSource N i
ftAdvSource N i j inc =
  Refinement.FTToAdversarialIncidence.sourceIsForcedTail inc

ftAdvTarget :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  AdversarialTarget N j
ftAdvTarget N i j inc =
  Refinement.FTToAdversarialIncidence.targetIsAdversarial inc

ftTransSource :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  ForcedTailSource N i
ftTransSource N i j inc =
  Refinement.FTToTransitionIncidence.sourceIsForcedTail inc

ftTransTarget :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  TransitionTarget N j
ftTransTarget N i j inc =
  Refinement.FTToTransitionIncidence.targetIsTransition inc

ftAdvDepthSeparationLinear :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  entryDepth i + advLogDepthRequired N ≤ entryDepth j
ftAdvDepthSeparationLinear N i j inc =
  ≤-trans
    (+-mono-≤
      (forcedTailSourceDepthUpper N i (ftAdvSource N i j inc))
      (≤-refl {advLogDepthRequired N}))
    (adversarialTargetDepthLower N j (ftAdvTarget N i j inc))

ftAdvDepthOrderingFromLinear :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  entryDepth i ≤ entryDepth j
ftAdvDepthOrderingFromLinear N i j inc =
  ≤-trans
    (m≤m+n (entryDepth i) (advLogDepthRequired N))
    (ftAdvDepthSeparationLinear N i j inc)

ftAdvProfileSeparationFromLinear :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  advLogDepthRequired N ≤ entryDepth j ∸ entryDepth i
ftAdvProfileSeparationFromLinear N i j inc =
  m+n≤p→n≤p∸m (entryDepth i) (advLogDepthRequired N) (entryDepth j)
    (ftAdvDepthSeparationLinear N i j inc)

ftTransDepthSeparationLinear :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  entryDepth i + transLogDepthRequired N ≤ entryDepth j
ftTransDepthSeparationLinear N i j inc =
  ≤-trans
    (+-mono-≤
      (forcedTailSourceDepthUpper N i (ftTransSource N i j inc))
      (≤-refl {transLogDepthRequired N}))
    (transitionTargetDepthLower N j (ftTransTarget N i j inc))

ftTransDepthOrderingFromLinear :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  entryDepth i ≤ entryDepth j
ftTransDepthOrderingFromLinear N i j inc =
  ≤-trans
    (m≤m+n (entryDepth i) (transLogDepthRequired N))
    (ftTransDepthSeparationLinear N i j inc)

ftTransProfileSeparationFromLinear :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  transLogDepthRequired N ≤ entryDepth j ∸ entryDepth i
ftTransProfileSeparationFromLinear N i j inc =
  m+n≤p→n≤p∸m (entryDepth i) (transLogDepthRequired N) (entryDepth j)
    (ftTransDepthSeparationLinear N i j inc)

canonicalFTAdvDepthGeometry : FTToAdversarialDepthGeometry
canonicalFTAdvDepthGeometry = record
  { logDepthRequired = advLogDepthRequired
  ; depthOrdering = ftAdvDepthOrderingFromLinear
  ; profileSeparation = ftAdvProfileSeparationFromLinear
  ; logDepthRequiredBound = pow2GeqSucN
  }

canonicalFTTransDepthGeometry : FTToTransitionDepthGeometry
canonicalFTTransDepthGeometry = record
  { logDepthRequired = transLogDepthRequired
  ; depthOrdering = ftTransDepthOrderingFromLinear
  ; profileSeparation = ftTransProfileSeparationFromLinear
  ; logDepthRequiredBound = pow2GeqSucN
  }

ftAdvDepthOrdering :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  entryDepth i ≤ entryDepth j
ftAdvDepthOrdering =
  FTToAdversarialDepthGeometry.depthOrdering canonicalFTAdvDepthGeometry

ftTransDepthOrdering :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  entryDepth i ≤ entryDepth j
ftTransDepthOrdering =
  FTToTransitionDepthGeometry.depthOrdering canonicalFTTransDepthGeometry

ftAdvProfileSeparation :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  FTToAdversarialDepthGeometry.logDepthRequired canonicalFTAdvDepthGeometry N
    ≤ entryDepth j ∸ entryDepth i
ftAdvProfileSeparation =
  FTToAdversarialDepthGeometry.profileSeparation canonicalFTAdvDepthGeometry

ftTransProfileSeparation :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  FTToTransitionDepthGeometry.logDepthRequired canonicalFTTransDepthGeometry N
    ≤ entryDepth j ∸ entryDepth i
ftTransProfileSeparation =
  FTToTransitionDepthGeometry.profileSeparation canonicalFTTransDepthGeometry

pow2LogDepthRequiredAdv :
  (N : Nat) →
  suc N ≤ pow2 (FTToAdversarialDepthGeometry.logDepthRequired canonicalFTAdvDepthGeometry N)
pow2LogDepthRequiredAdv =
  FTToAdversarialDepthGeometry.logDepthRequiredBound canonicalFTAdvDepthGeometry

pow2LogDepthRequiredTrans :
  (N : Nat) →
  suc N ≤ pow2 (FTToTransitionDepthGeometry.logDepthRequired canonicalFTTransDepthGeometry N)
pow2LogDepthRequiredTrans =
  FTToTransitionDepthGeometry.logDepthRequiredBound canonicalFTTransDepthGeometry

ftAdvDepthGainEnough :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  suc N ≤ pow2 (entryDepth j ∸ entryDepth i)
ftAdvDepthGainEnough N i j inc =
  ≤-trans
    (pow2LogDepthRequiredAdv N)
    (pow2-mono (ftAdvProfileSeparation N i j inc))

ftTransDepthGainEnough :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  suc N ≤ pow2 (entryDepth j ∸ entryDepth i)
ftTransDepthGainEnough N i j inc =
  ≤-trans
    (pow2LogDepthRequiredTrans N)
    (pow2-mono (ftTransProfileSeparation N i j inc))

-----------------------------------------------------------------------
-- Derived: weight separation theorems for Blocker 1.
--
-- From ftAdvDepthGainEnough we get 2^{d_j ∸ d_i} ≥ N + 1.
-- Together with depth ordering and the depthWeightSeparation lemma,
-- this gives (suc N) · w(j) ≤ w(i).
--
-- Chain:
--   1. d_i ≤ d_j                                        (ftAdvDepthOrdering)
--   2. suc N ≤ pow2 (d_j ∸ d_i)                         (ftAdvDepthGainEnough)
--   3. Set k = d_j ∸ d_i.  Then d_i + k ≤ d_j           (by m+[n∸m]≤n from 1)
--   4. d_i ≤ M, d_j ≤ M                                 (entryDepthBound)
--   5. pow2 k · w(j) ≤ w(i)                             (depthWeightSeparation)
--   6. suc N ≤ pow2 k = 2^{d_j ∸ d_i}                   (from 2)
--   7. Therefore (suc N) · w(j) ≤ pow2 k · w(j) ≤ w(i)
-----------------------------------------------------------------------

ftAdvWeightSeparation :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  suc N * weightOf j ≤ weightOf i
ftAdvWeightSeparation N i j inc =
  let
    d_i = entryDepth i
    d_j = entryDepth j
    k   = d_j ∸ d_i

    d_i≤d_j  = ftAdvDepthOrdering N i j inc
    d_i≤M    = entryDepthBound i
    d_j≤M    = entryDepthBound j
    sucN≤p2k = ftAdvDepthGainEnough N i j inc
    di+k≤dj  = m+[n∸m]≤n d_i≤d_j
    p2k·wj≤wi = depthWeightSeparation i j k d_i≤M d_j≤M di+k≤dj

  in
    ≤-trans
      (*-mono-≤ sucN≤p2k (≤-refl {weightOf j}))
      p2k·wj≤wi

ftTransWeightSeparation :
  (N i j : Nat) →
  Refinement.FTToTransitionIncidence N i j →
  suc N * weightOf j ≤ weightOf i
ftTransWeightSeparation N i j inc =
  let
    d_i = entryDepth i
    d_j = entryDepth j
    k   = d_j ∸ d_i

    d_i≤d_j  = ftTransDepthOrdering N i j inc
    d_i≤M    = entryDepthBound i
    d_j≤M    = entryDepthBound j
    sucN≤p2k = ftTransDepthGainEnough N i j inc
    di+k≤dj  = m+[n∸m]≤n d_i≤d_j
    p2k·wj≤wi = depthWeightSeparation i j k d_i≤M d_j≤M di+k≤dj

  in
    ≤-trans
      (*-mono-≤ sucN≤p2k (≤-refl {weightOf j}))
      p2k·wj≤wi

-----------------------------------------------------------------------
-- Bridge: the weight model's weightOf agrees with the refinement
-- file's postulate pointwise.
--
-- The refinement file postulates weightOf : Nat → Nat but does not
-- constrain it further.  The weight model defines weightOf
-- concretely as 2^{maxDepth − entryDepth k}.  The bridge postulate
-- asserts that the two coincide on every index, which is true by
-- definitional intent (the refinement was designed to be instantiated
-- by this weight model).
-----------------------------------------------------------------------

postulate
  weightOf-≡ : ∀ k → weightOf k ≡ Refinement.weightOf k

weightOf-≤ : ∀ k → weightOf k ≤ Refinement.weightOf k
weightOf-≤ k = ≤-reflexive (weightOf-≡ k)

refinementWeightOf-≤ : ∀ k → Refinement.weightOf k ≤ weightOf k
refinementWeightOf-≤ k = ≤-reflexive (sym (weightOf-≡ k))

-----------------------------------------------------------------------
-- Canonical inhabitants for the refinement file's weight orientation
-- gain records.
--
-- These lift ftAdvWeightSeparation / ftTransWeightSeparation from
-- the weight model's weightOf to the refinement file's weightOf
-- via the pointwise equality bridge.
-----------------------------------------------------------------------

canonicalFTAdvWeightOrientationGain :
  Refinement.ForcedTailAdversarialWeightOrientationGain
canonicalFTAdvWeightOrientationGain =
  Refinement.mkForcedTailAdversarialWeightOrientationGain bridge
  where
    bridge : (N i j : Nat) →
             Refinement.FTToAdversarialIncidence N i j →
             suc N * Refinement.weightOf j ≤ Refinement.weightOf i
    bridge N i j inc =
      let
        inner = ftAdvWeightSeparation N i j inc
      in
      ≤-trans
        (*-mono-≤ (≤-refl {suc N}) (refinementWeightOf-≤ j))
        (≤-trans inner (weightOf-≤ i))

canonicalFTTransWeightOrientationGain :
  Refinement.ForcedTailTransitionWeightOrientationGain
canonicalFTTransWeightOrientationGain =
  Refinement.mkForcedTailTransitionWeightOrientationGain bridge
  where
    bridge : (N i j : Nat) →
             Refinement.FTToTransitionIncidence N i j →
             suc N * Refinement.weightOf j ≤ Refinement.weightOf i
    bridge N i j inc =
      let
        inner = ftTransWeightSeparation N i j inc
      in
      ≤-trans
        (*-mono-≤ (≤-refl {suc N}) (refinementWeightOf-≤ j))
        (≤-trans inner (weightOf-≤ i))

-----------------------------------------------------------------------
-- Honest status.
-----------------------------------------------------------------------

pow2GeqSucNProved : Bool
pow2GeqSucNProved = true

depthWeightSeparationProved : Bool
depthWeightSeparationProved = true

ftAdvDepthGainEnoughProved : Bool
ftAdvDepthGainEnoughProved = false

ftTransDepthGainEnoughProved : Bool
ftTransDepthGainEnoughProved = false

ftAdvDepthOrderingProved : Bool
ftAdvDepthOrderingProved = false

ftTransDepthOrderingProved : Bool
ftTransDepthOrderingProved = false

weightSeparationProved : Bool
weightSeparationProved = false
-- Set to true only when ftAdvDepthGainEnough, ftTransDepthGainEnough
-- and the corresponding depth ordering postulates are proved, or when
-- an alternative route (count gain, magnitude gain, profile incompatibility)
-- bypasses the depth-weight chain entirely.
