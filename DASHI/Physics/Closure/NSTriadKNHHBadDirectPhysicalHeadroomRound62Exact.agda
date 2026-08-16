module DASHI.Physics.Closure.NSTriadKNHHBadDirectPhysicalHeadroomRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 CONTRIBUTION
--
-- The later HH-bad proof no longer needs the old alpha/beta affine recurrence.
-- Work directly with the selected physical shell source.  The ONLY dynamical
-- identity retained here is the literal successor decomposition
--
-- B_(q+1)
--   = delta 2^(-(q+1)) I_(q+1) + G_q + L_q.
--
-- Normalize by delta^(-1) 2^(q+1).  Exact reciprocal cancellation gives
--
-- C_(q+1) = I_(q+1) + N_q.
--
-- Therefore N_q <= C_* - I_(q+1) preserves the ceiling in one step.  An
-- arbitrary finite prefix plus this tail headroom proves C_q<=C_* globally.
-- No alpha contraction, beta factorization, or manufactured recurrence
-- coefficient is required.
--
-- A literal density satisfying 2^q g_q <= C_q is then transported directly
-- to the mature selected-threshold HH-bad profile.  This is the A1/A2/A3 shape
-- of the physical Clay cutset with every later recurrence convenience removed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalDuhamelSourceRound59 as Source
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteTransientTailBarrierRound55Exact as Tail
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected

record DirectPhysicalDuhamelIdentity
    (source : Source.PhysicalLocalizedDuhamelSource) : Set where
  field
    successorDecomposition : ∀ q →
      Source.defectAt source (suc q)
      ≡ Threshold.threshold (Source.parameter source)
          * Sharp.inverseDyadicScale (suc q)
          * Source.inheritedAt source (suc q)
        + Source.generatedAt source q + Source.leakageAt source q

open DirectPhysicalDuhamelIdentity public

threshold : Source.PhysicalLocalizedDuhamelSource → ℚ
threshold source = Threshold.threshold (Source.parameter source)

thresholdInverse : Source.PhysicalLocalizedDuhamelSource → ℚ
thresholdInverse source = Threshold.thresholdInverse (Source.parameter source)

normalizedDefect : Source.PhysicalLocalizedDuhamelSource → Nat → ℚ
normalizedDefect source q =
  thresholdInverse source * Sharp.dyadicScale q * Source.defectAt source q

literalNormalizedInherited :
  Source.PhysicalLocalizedDuhamelSource → Nat → ℚ
literalNormalizedInherited source q = Source.inheritedAt source (suc q)

literalNormalizedGeneration :
  Source.PhysicalLocalizedDuhamelSource → Nat → ℚ
literalNormalizedGeneration source q =
  thresholdInverse source * Sharp.dyadicScale (suc q)
    * (Source.generatedAt source q + Source.leakageAt source q)

normalizedInheritedCancellation :
  (source : Source.PhysicalLocalizedDuhamelSource) → ∀ q →
  thresholdInverse source * Sharp.dyadicScale (suc q)
    * (threshold source * Sharp.inverseDyadicScale (suc q)
      * Source.inheritedAt source (suc q))
  ≡ literalNormalizedInherited source q
normalizedInheritedCancellation source q =
  let
    inv = thresholdInverse source
    delta = threshold source
    dy = Sharp.dyadicScale (suc q)
    idy = Sharp.inverseDyadicScale (suc q)
    inherited = Source.inheritedAt source (suc q)

    regroup :
      (inv * dy) * (delta * idy * inherited)
      ≡ (inv * delta) * (idy * dy) * inherited
    regroup = solve (inv ∷ dy ∷ delta ∷ idy ∷ inherited ∷ [])
  in
  trans regroup
    (trans
      (cong (λ first → first * (idy * dy) * inherited)
        (Threshold.inverseMeaning (Source.parameter source)))
      (trans
        (cong (λ second → 1ℚ * second * inherited)
          (Sharp.inverseDyadicReciprocal (suc q)))
        (solve (inherited ∷ []))))

normalizedSuccessorComponentsExact :
  (source : Source.PhysicalLocalizedDuhamelSource) →
  DirectPhysicalDuhamelIdentity source → ∀ q →
  normalizedDefect source (suc q)
  ≡ literalNormalizedInherited source q
      + literalNormalizedGeneration source q
normalizedSuccessorComponentsExact source identity q =
  let
    factor = thresholdInverse source * Sharp.dyadicScale (suc q)
    generated = Source.generatedAt source q
    leakage = Source.leakageAt source q
    inheritedTerm =
      threshold source * Sharp.inverseDyadicScale (suc q)
        * Source.inheritedAt source (suc q)

    distributed :
      factor * (inheritedTerm + generated + leakage)
      ≡ factor * inheritedTerm + factor * (generated + leakage)
    distributed = solve (factor ∷ inheritedTerm ∷ generated ∷ leakage ∷ [])
  in
  trans
    (cong (factor *_) (successorDecomposition identity q))
    (trans distributed
      (cong
        (λ inherited → inherited + literalNormalizedGeneration source q)
        (normalizedInheritedCancellation source q)))

literalGenerationFitsInheritedHeadroom :
  Source.PhysicalLocalizedDuhamelSource → ℚ → Nat → Set
literalGenerationFitsInheritedHeadroom source ceiling q =
  literalNormalizedGeneration source q
  ≤ ceiling - literalNormalizedInherited source q

headroomPreservesCeiling :
  (source : Source.PhysicalLocalizedDuhamelSource) →
  (identity : DirectPhysicalDuhamelIdentity source) →
  (ceiling : ℚ) → ∀ q →
  literalGenerationFitsInheritedHeadroom source ceiling q →
  normalizedDefect source (suc q) ≤ ceiling
headroomPreservesCeiling source identity ceiling q headroom =
  let
    inherited = literalNormalizedInherited source q
    generated = literalNormalizedGeneration source q
    added : inherited + generated ≤ inherited + (ceiling - inherited)
    added = ℚP.+-monoˡ-≤ inherited headroom
    closes : inherited + (ceiling - inherited) ≡ ceiling
    closes = solve (inherited ∷ ceiling ∷ [])
  in
  subst
    (λ left → left ≤ ceiling)
    (sym (normalizedSuccessorComponentsExact source identity q))
    (subst (λ right → inherited + generated ≤ right) closes added)

record DirectPhysicalTailHeadroom
    (source : Source.PhysicalLocalizedDuhamelSource)
    (identity : DirectPhysicalDuhamelIdentity source) : Set where
  field
    start : Nat
    ceiling : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling

    finitePrefixBelow : ∀ q → q Nat.≤ start →
      normalizedDefect source q ≤ ceiling

    tailComponentHeadroom : ∀ q → start Nat.≤ q →
      literalGenerationFitsInheritedHeadroom source ceiling q

open DirectPhysicalTailHeadroom public

tailBelowCeiling :
  ∀ {source identity}
    (capacity : DirectPhysicalTailHeadroom source identity) {q} →
  Tail.TailAt (start capacity) q →
  normalizedDefect source q ≤ ceiling capacity
tailBelowCeiling capacity Tail.atStart =
  finitePrefixBelow capacity (start capacity) NatP.≤-refl
tailBelowCeiling {source} {identity} capacity (Tail.atStep {q} previous) =
  headroomPreservesCeiling source identity (ceiling capacity) q
    (tailComponentHeadroom capacity q (Tail.tailAtOrder previous))

globalNormalizedDefectBelowCeiling :
  ∀ {source identity}
    (capacity : DirectPhysicalTailHeadroom source identity) q →
  normalizedDefect source q ≤ ceiling capacity
globalNormalizedDefectBelowCeiling capacity q
  with Tail.splitPrefixOrTail (start capacity) q
... | Tail.prefix proof = finitePrefixBelow capacity q proof
... | Tail.tail witness = tailBelowCeiling capacity witness

record DirectPhysicalDensityDomination
    (effectiveViscosity : ℚ)
    (source : Source.PhysicalLocalizedDuhamelSource)
    (identity : DirectPhysicalDuhamelIdentity source)
    (capacity : DirectPhysicalTailHeadroom source identity) : Set where
  field
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedDensityBelowDefect : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ normalizedDefect source shell

open DirectPhysicalDensityDomination public

directSelectedThresholdProfile :
  ∀ {effectiveViscosity source identity capacity} →
  DirectPhysicalDensityDomination
    effectiveViscosity source identity capacity →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
directSelectedThresholdProfile {source = source} {capacity = capacity} densityData = record
  { selectedThreshold = Source.parameter source
  ; density = density densityData
  ; densityNonnegative = densityNonnegative densityData
  ; cells = cells densityData
  ; selectedProfileCeiling = ceiling capacity
  ; selectedProfileCeilingNonnegative = ceilingNonnegative capacity
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedDensityBelowDefect densityData shell)
        (globalNormalizedDefectBelowCeiling capacity shell)
  }

directAUsesOnlyLiteralIdentityHeadroomAndDensityDomination : Bool
directAUsesOnlyLiteralIdentityHeadroomAndDensityDomination = true

directAUsesOnlyLiteralIdentityHeadroomAndDensityDominationIsTrue :
  directAUsesOnlyLiteralIdentityHeadroomAndDensityDomination ≡ true
directAUsesOnlyLiteralIdentityHeadroomAndDensityDominationIsTrue = refl
