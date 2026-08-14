module DASHI.Physics.Closure.NSTriadKNHHBadLiteralComponentCapacityRound57Exact where

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
-- ROUND 57 CONTRIBUTION
--
-- Remove alpha from the final HH-bad tail comparison altogether. The physical
-- Duhamel carrier already contains the literal inherited, generated and
-- leakage terms, so normalize those actual components and prove the exact
-- successor identity
--
--   C_(q+1) = I^lit_q + N^lit_q.
--
-- A ceiling C_* is therefore preserved whenever
--
--   N^lit_q <= C_* - I^lit_q.
--
-- The final theorem permits an arbitrary finite prefix and uses only this
-- literal component-headroom comparison on the tail.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralNormalizedGenerationRound57Exact as Lit
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteTransientTailBarrierRound55Exact as Tail

literalNormalizedInherited :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
literalNormalizedInherited physical q =
  Raw.normalizationFactor physical (suc q) * Raw.inherited physical q

literalNormalizedSuccessorComponentsExact :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  Raw.normalizedDefect physical (suc q)
  ≡ literalNormalizedInherited physical q
      + Lit.literalNormalizedGeneration physical q
literalNormalizedSuccessorComponentsExact physical q =
  let
    factor = Raw.normalizationFactor physical (suc q)
    source = Raw.successorDecomposition physical q
    distribute :
      factor
        * (Raw.inherited physical q
          + Raw.generated physical q
          + Raw.leakage physical q)
      ≡
      factor * Raw.inherited physical q
        + factor * (Raw.generated physical q + Raw.leakage physical q)
    distribute =
      solve
        ( factor
        ∷ Raw.inherited physical q
        ∷ Raw.generated physical q
        ∷ Raw.leakage physical q
        ∷ [])
  in
  trans
    (cong (factor *_) source)
    distribute

literalGenerationFitsInheritedHeadroom :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  (ceiling : ℚ) → Nat → Set
literalGenerationFitsInheritedHeadroom physical ceiling q =
  Lit.literalNormalizedGeneration physical q
  ≤ ceiling - literalNormalizedInherited physical q

literalComponentHeadroomPreservesCeiling :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  (ceiling : ℚ) →
  ∀ q →
  literalGenerationFitsInheritedHeadroom physical ceiling q →
  Raw.normalizedDefect physical (suc q) ≤ ceiling
literalComponentHeadroomPreservesCeiling physical ceiling q generationFits =
  let
    inherited = literalNormalizedInherited physical q
    generated = Lit.literalNormalizedGeneration physical q
    addInherited :
      inherited + generated ≤ inherited + (ceiling - inherited)
    addInherited = ℚP.+-monoˡ-≤ inherited generationFits
    closes : inherited + (ceiling - inherited) ≡ ceiling
    closes = solve (inherited ∷ ceiling ∷ [])
    componentBound : inherited + generated ≤ ceiling
    componentBound =
      subst
        (λ right → inherited + generated ≤ right)
        closes
        addInherited
  in
  subst
    (λ left → left ≤ ceiling)
    (sym (literalNormalizedSuccessorComponentsExact physical q))
    componentBound

record LiteralComponentTailCapacity
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    start : Nat
    ceiling : ℚ
    finitePrefixBelow : ∀ q → q Nat.≤ start →
      Raw.normalizedDefect physical q ≤ ceiling
    tailComponentHeadroom : ∀ q → start Nat.≤ q →
      literalGenerationFitsInheritedHeadroom physical ceiling q

open LiteralComponentTailCapacity public

literalComponentTailBelow :
  ∀ {physical}
    (capacity : LiteralComponentTailCapacity physical) {q} →
  Tail.TailAt (start capacity) q →
  Raw.normalizedDefect physical q ≤ ceiling capacity
literalComponentTailBelow capacity Tail.atStart =
  finitePrefixBelow capacity (start capacity) NatP.≤-refl
literalComponentTailBelow {physical} capacity (Tail.atStep {q} previous) =
  literalComponentHeadroomPreservesCeiling
    physical (ceiling capacity) q
    (tailComponentHeadroom capacity q (Tail.tailAtOrder previous))

literalComponentGlobalBelow :
  ∀ {physical}
    (capacity : LiteralComponentTailCapacity physical) q →
  Raw.normalizedDefect physical q ≤ ceiling capacity
literalComponentGlobalBelow capacity q
  with Tail.splitPrefixOrTail (start capacity) q
... | Tail.prefix prefix = finitePrefixBelow capacity q prefix
... | Tail.tail tail = literalComponentTailBelow capacity tail

literalComponentCapacityUsesNoAlpha : Bool
literalComponentCapacityUsesNoAlpha = true

literalComponentTailAllowsArbitraryFiniteTransient : Bool
literalComponentTailAllowsArbitraryFiniteTransient = true

literalComponentCapacityUsesNoAlphaIsTrue :
  literalComponentCapacityUsesNoAlpha ≡ true
literalComponentCapacityUsesNoAlphaIsTrue = refl

literalComponentTailAllowsArbitraryFiniteTransientIsTrue :
  literalComponentTailAllowsArbitraryFiniteTransient ≡ true
literalComponentTailAllowsArbitraryFiniteTransientIsTrue = refl
