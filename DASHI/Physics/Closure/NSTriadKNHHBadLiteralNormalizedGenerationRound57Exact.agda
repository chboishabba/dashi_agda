module DASHI.Physics.Closure.NSTriadKNHHBadLiteralNormalizedGenerationRound57Exact where

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
-- Do not leave beta_q as a free diagnostic when the literal inherited /
-- generated / leakage carrier is already present.  Normalize the ACTUAL
-- generated+leakage contribution itself:
--
--   beta^lit_q := delta_*^{-1} 2^(q+1) (G_q + L_q).
--
-- Then prove directly
--
--   C_(q+1) <= alpha_q C_q + beta^lit_q.
--
-- Consequently the tail theorem can consume the physically transparent
-- comparison
--
--   beta^lit_q <= (1-alpha_q) C_*
--
-- after an arbitrary finite prefix.  No abstract forcing majorant, uniform
-- contraction constant, or raw summability theorem is used in this lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as Nat
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteTransientTailBarrierRound55Exact as Tail
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

literalGeneratedLeakage :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
literalGeneratedLeakage physical q =
  Raw.generated physical q + Raw.leakage physical q

literalNormalizedGeneration :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
literalNormalizedGeneration physical q =
  Raw.normalizationFactor physical (suc q)
    * literalGeneratedLeakage physical q

literalGeneratedLeakageNonnegative :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q → 0ℚ ≤ literalGeneratedLeakage physical q
literalGeneratedLeakageNonnegative physical q =
  ℚP.+-mono-≤
    (Raw.generatedNonnegative physical q)
    (Raw.leakageNonnegative physical q)

literalNormalizedGenerationNonnegative :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q → 0ℚ ≤ literalNormalizedGeneration physical q
literalNormalizedGenerationNonnegative physical q =
  let instance
    factorNN = nonNegative (Raw.normalizationFactorNonnegative physical (suc q))
    sourceNN = nonNegative (literalGeneratedLeakageNonnegative physical q)
  in ℚP.nonNegative⁻¹ (literalNormalizedGeneration physical q)

literalComponentTransfer :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  Raw.defectRate physical (suc q)
  ≤ Raw.alpha physical q * Sharp.half * Raw.defectRate physical q
      + literalGeneratedLeakage physical q
literalComponentTransfer physical q =
  let
    inheritedBound = Raw.inheritedTransfer physical q
    keepLiteralGeneration :
      literalGeneratedLeakage physical q
      ≤ literalGeneratedLeakage physical q
    keepLiteralGeneration = ℚP.≤-refl
    summed = ℚP.+-mono-≤ inheritedBound keepLiteralGeneration
    sourceMeaning :
      Raw.defectRate physical (suc q)
      ≡ Raw.inherited physical q + literalGeneratedLeakage physical q
    sourceMeaning =
      trans
        (Raw.successorDecomposition physical q)
        (solve
          ( Raw.inherited physical q
          ∷ Raw.generated physical q
          ∷ Raw.leakage physical q
          ∷ []))
  in
  subst
    (λ left →
      left
      ≤ Raw.alpha physical q * Sharp.half * Raw.defectRate physical q
          + literalGeneratedLeakage physical q)
    (sym sourceMeaning)
    summed

literalNormalizedRecurrence :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  Raw.normalizedDefect physical (suc q)
  ≤ Raw.alpha physical q * Raw.normalizedDefect physical q
      + literalNormalizedGeneration physical q
literalNormalizedRecurrence physical q =
  let
    factor = Raw.normalizationFactor physical (suc q)
    scaled :
      factor * Raw.defectRate physical (suc q)
      ≤ factor
        * (Raw.alpha physical q * Sharp.half * Raw.defectRate physical q
          + literalGeneratedLeakage physical q)
    scaled =
      let instance factorNN =
        nonNegative (Raw.normalizationFactorNonnegative physical (suc q))
      in ℚP.*-monoˡ-≤-nonNeg factor (literalComponentTransfer physical q)

    rhsMeaning :
      factor
        * (Raw.alpha physical q * Sharp.half * Raw.defectRate physical q
          + literalGeneratedLeakage physical q)
      ≡ Raw.alpha physical q * Raw.normalizedDefect physical q
          + literalNormalizedGeneration physical q
    rhsMeaning =
      trans
        (solve
          ( factor
          ∷ Raw.alpha physical q
          ∷ Raw.defectRate physical q
          ∷ literalGeneratedLeakage physical q
          ∷ []))
        (cong₂ _+_
          (Raw.normalizedInheritedIdentity physical q)
          refl)
  in
  subst
    (λ right → Raw.normalizedDefect physical (suc q) ≤ right)
    rhsMeaning
    scaled

record LiteralTailDepletion
    (physical : Raw.PhysicalGeneralVariableDefectDuhamel) : Set where
  field
    start : Nat
    ceiling : ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling

    finitePrefixBelow : ∀ q → q Nat.≤ start →
      Raw.normalizedDefect physical q ≤ ceiling

    -- This is the actual shellwise physical balance sought from Duhamel:
    -- normalized generated+leaked defect is no larger than the capacity
    -- replenished by inherited depletion.
    generatedLeakageBelowInheritedDepletion : ∀ q → start Nat.≤ q →
      literalNormalizedGeneration physical q
      ≤ (1ℚ - Raw.alpha physical q) * ceiling

open LiteralTailDepletion public

literalTailStepPreservesCeiling :
  ∀ {physical}
    (depletion : LiteralTailDepletion physical) q →
  start depletion Nat.≤ q →
  Raw.normalizedDefect physical q ≤ ceiling depletion →
  Raw.normalizedDefect physical (suc q) ≤ ceiling depletion
literalTailStepPreservesCeiling {physical} depletion q tailOrder current =
  let
    inheritedScaled :
      Raw.alpha physical q * Raw.normalizedDefect physical q
      ≤ Raw.alpha physical q * ceiling depletion
    inheritedScaled =
      let instance alphaNN = nonNegative (Raw.alphaNonnegative physical q)
      in ℚP.*-monoˡ-≤-nonNeg (Raw.alpha physical q) current

    generated = generatedLeakageBelowInheritedDepletion depletion q tailOrder

    combined :
      Raw.alpha physical q * Raw.normalizedDefect physical q
        + literalNormalizedGeneration physical q
      ≤ Raw.alpha physical q * ceiling depletion
        + (1ℚ - Raw.alpha physical q) * ceiling depletion
    combined = ℚP.+-mono-≤ inheritedScaled generated

    recurrenceThenBalance :
      Raw.normalizedDefect physical (suc q)
      ≤ Raw.alpha physical q * ceiling depletion
        + (1ℚ - Raw.alpha physical q) * ceiling depletion
    recurrenceThenBalance =
      ℚP.≤-trans (literalNormalizedRecurrence physical q) combined

    balance :
      Raw.alpha physical q * ceiling depletion
        + (1ℚ - Raw.alpha physical q) * ceiling depletion
      ≡ ceiling depletion
    balance = solve (Raw.alpha physical q ∷ ceiling depletion ∷ [])
  in
  subst
    (λ upper → Raw.normalizedDefect physical (suc q) ≤ upper)
    balance
    recurrenceThenBalance

literalTailBelow :
  ∀ {physical} (depletion : LiteralTailDepletion physical) {q} →
  Tail.TailAt (start depletion) q →
  Raw.normalizedDefect physical q ≤ ceiling depletion
literalTailBelow depletion Tail.atStart =
  finitePrefixBelow depletion (start depletion) Nat.≤-refl
literalTailBelow depletion (Tail.atStep {q} witness) =
  literalTailStepPreservesCeiling depletion q
    (Tail.tailAtOrder witness)
    (literalTailBelow depletion witness)

globalLiteralDefectBelowCeiling :
  ∀ {physical} (depletion : LiteralTailDepletion physical) q →
  Raw.normalizedDefect physical q ≤ ceiling depletion
globalLiteralDefectBelowCeiling depletion q
  with Tail.splitPrefixOrTail (start depletion) q
... | Tail.prefix proof = finitePrefixBelow depletion q proof
... | Tail.tail witness = literalTailBelow depletion witness

literalBetaIsActualGeneratedLeakageNotAbstractForcing : Bool
literalBetaIsActualGeneratedLeakageNotAbstractForcing = true

round57HHBadPhysicalComparisonIsSingleTailInequality : Bool
round57HHBadPhysicalComparisonIsSingleTailInequality = true

literalBetaIsActualGeneratedLeakageNotAbstractForcingIsTrue :
  literalBetaIsActualGeneratedLeakageNotAbstractForcing ≡ true
literalBetaIsActualGeneratedLeakageNotAbstractForcingIsTrue = refl

round57HHBadPhysicalComparisonIsSingleTailInequalityIsTrue :
  round57HHBadPhysicalComparisonIsSingleTailInequality ≡ true
round57HHBadPhysicalComparisonIsSingleTailInequalityIsTrue = refl
