module DASHI.Physics.Closure.NSTriadKNLowerThreeCriticalOwnersRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The finite Bony lane already proves the *total* four-class terminal bound
--
--   LH + HL + CC + HH->low <= (1/64) E_q
--
-- once the critical terminal root is small.  For the positive-production
-- owner ledger, the three lower-risk local classes LH/HL/CC are themselves
-- nonnegative.  Therefore each one is bounded by the same total.  If the
-- physical shell energy is a subcharge of the global dissipation carried by
-- TaxEnvironment, each of these three owners consumes at most 1/64 of the
-- viscosity reserve.
--
-- This module performs that extraction exactly.  It does not relabel the
-- HH->low term as the separate `tail` owner: that semantic identification must
-- be proved by the physical decomposition and is intentionally not guessed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Bony
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical

record PhysicalLowerThreeCriticalOwnerInput
    (environment : Owner.TaxEnvironment) : Set where
  field
    closureData : Critical.CriticalFourClassClosureData

    lowHighNonnegative :
      0ℚ ≤ Bony.lowHigh (Critical.budget closureData)
    highLowNonnegative :
      0ℚ ≤ Bony.highLow (Critical.budget closureData)
    comparableNonnegative :
      0ℚ ≤ Bony.comparable (Critical.budget closureData)
    highHighToLowNonnegative :
      0ℚ ≤ Bony.highHighToLow (Critical.budget closureData)

    shellEnergyBelowDissipation :
      Bony.shellEnergy (Critical.budget closureData)
      ≤ Owner.dissipation environment

open PhysicalLowerThreeCriticalOwnerInput public

remainingAfterLHNonnegative :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  0ℚ ≤
    Bony.highLow (Critical.budget (closureData input))
    + Bony.comparable (Critical.budget (closureData input))
    + Bony.highHighToLow (Critical.budget (closureData input))
remainingAfterLHNonnegative input =
  L2.addNonnegative
    (L2.addNonnegative
      (highLowNonnegative input)
      (comparableNonnegative input))
    (highHighToLowNonnegative input)

remainingAfterHLNonnegative :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  0ℚ ≤
    Bony.lowHigh (Critical.budget (closureData input))
    + Bony.comparable (Critical.budget (closureData input))
    + Bony.highHighToLow (Critical.budget (closureData input))
remainingAfterHLNonnegative input =
  L2.addNonnegative
    (L2.addNonnegative
      (lowHighNonnegative input)
      (comparableNonnegative input))
    (highHighToLowNonnegative input)

remainingAfterCCNonnegative :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  0ℚ ≤
    Bony.lowHigh (Critical.budget (closureData input))
    + Bony.highLow (Critical.budget (closureData input))
    + Bony.highHighToLow (Critical.budget (closureData input))
remainingAfterCCNonnegative input =
  L2.addNonnegative
    (L2.addNonnegative
      (lowHighNonnegative input)
      (highLowNonnegative input))
    (highHighToLowNonnegative input)

lowHighBelowTotal :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  Bony.lowHigh (Critical.budget (closureData input))
  ≤ Bony.totalInteraction (Critical.budget (closureData input))
lowHighBelowTotal input =
  let
    b = Critical.budget (closureData input)
    addRest :
      Bony.lowHigh b + 0ℚ
      ≤ Bony.lowHigh b
        + (Bony.highLow b + Bony.comparable b + Bony.highHighToLow b)
    addRest = ℚP.+-monoʳ-≤ (Bony.lowHigh b)
      (remainingAfterLHNonnegative input)
  in
  subst
    (λ lower → lower ≤ Bony.totalInteraction b)
    (solve (Bony.lowHigh b ∷ []))
    (subst
      (λ upper → Bony.lowHigh b + 0ℚ ≤ upper)
      (sym (solve
        ( Bony.lowHigh b ∷ Bony.highLow b
        ∷ Bony.comparable b ∷ Bony.highHighToLow b ∷ [])))
      addRest)

highLowBelowTotal :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  Bony.highLow (Critical.budget (closureData input))
  ≤ Bony.totalInteraction (Critical.budget (closureData input))
highLowBelowTotal input =
  let
    b = Critical.budget (closureData input)
    rest = Bony.lowHigh b + Bony.comparable b + Bony.highHighToLow b
    addRest : Bony.highLow b + 0ℚ ≤ Bony.highLow b + rest
    addRest = ℚP.+-monoʳ-≤ (Bony.highLow b)
      (remainingAfterHLNonnegative input)
    target : Bony.highLow b + rest ≡ Bony.totalInteraction b
    target = solve
      ( Bony.lowHigh b ∷ Bony.highLow b
      ∷ Bony.comparable b ∷ Bony.highHighToLow b ∷ [])
  in
  subst
    (λ lower → lower ≤ Bony.totalInteraction b)
    (solve (Bony.highLow b ∷ []))
    (subst
      (λ upper → Bony.highLow b + 0ℚ ≤ upper)
      target
      addRest)

comparableBelowTotal :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment) →
  Bony.comparable (Critical.budget (closureData input))
  ≤ Bony.totalInteraction (Critical.budget (closureData input))
comparableBelowTotal input =
  let
    b = Critical.budget (closureData input)
    rest = Bony.lowHigh b + Bony.highLow b + Bony.highHighToLow b
    addRest : Bony.comparable b + 0ℚ ≤ Bony.comparable b + rest
    addRest = ℚP.+-monoʳ-≤ (Bony.comparable b)
      (remainingAfterCCNonnegative input)
    target : Bony.comparable b + rest ≡ Bony.totalInteraction b
    target = solve
      ( Bony.lowHigh b ∷ Bony.highLow b
      ∷ Bony.comparable b ∷ Bony.highHighToLow b ∷ [])
  in
  subst
    (λ lower → lower ≤ Bony.totalInteraction b)
    (solve (Bony.comparable b ∷ []))
    (subst
      (λ upper → Bony.comparable b + 0ℚ ≤ upper)
      target
      addRest)

classBelowGlobalDissipationAtOneSixtyFourth :
  ∀ {environment}
    (input : PhysicalLowerThreeCriticalOwnerInput environment)
    (production : ℚ) →
  production ≤ Bony.totalInteraction (Critical.budget (closureData input)) →
  production ≤ Critical.Critical.oneSixtyFourth * Owner.dissipation environment
classBelowGlobalDissipationAtOneSixtyFourth {environment} input production classBelow =
  let
    closure = closureData input
    b = Critical.budget closure
    totalBound :
      Bony.totalInteraction b
      ≤ Critical.Critical.oneSixtyFourth * Bony.shellEnergy b
    totalBound = Critical.criticalFourClassTerminalClosure closure

    scaledShell :
      Critical.Critical.oneSixtyFourth * Bony.shellEnergy b
      ≤ Critical.Critical.oneSixtyFourth * Owner.dissipation environment
    scaledShell =
      let
        cNN : 0ℚ ≤ Critical.Critical.oneSixtyFourth
        cNN = ℚP.nonNegative⁻¹ Critical.Critical.oneSixtyFourth
        instance cNNI = nonNegative cNN
      in
      ℚP.*-monoˡ-≤-nonNeg Critical.Critical.oneSixtyFourth
        (shellEnergyBelowDissipation input)
  in
  ℚP.≤-trans classBelow (ℚP.≤-trans totalBound scaledShell)

physicalLHOwnerEstimate :
  ∀ {environment} →
  PhysicalLowerThreeCriticalOwnerInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalLHOwnerEstimate {environment} input =
  Owner.admissible-owner-estimate
    Tax.LH
    (Bony.lowHigh b)
    Critical.Critical.oneSixtyFourth
    0ℚ 0ℚ
    ownerBound
  where
  b = Critical.budget (closureData input)
  direct = classBelowGlobalDissipationAtOneSixtyFourth
    input (Bony.lowHigh b) (lowHighBelowTotal input)
  ownerBound :
    Bony.lowHigh b
    ≤ Critical.Critical.oneSixtyFourth * Owner.dissipation environment
      + 0ℚ + 0ℚ * Owner.integralCritical environment
  ownerBound = subst
    (λ upper → Bony.lowHigh b ≤ upper)
    (sym (solve
      (Critical.Critical.oneSixtyFourth ∷ Owner.dissipation environment ∷ [])))
    direct

physicalHLOwnerEstimate :
  ∀ {environment} →
  PhysicalLowerThreeCriticalOwnerInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalHLOwnerEstimate {environment} input =
  Owner.admissible-owner-estimate
    Tax.HL
    (Bony.highLow b)
    Critical.Critical.oneSixtyFourth
    0ℚ 0ℚ
    ownerBound
  where
  b = Critical.budget (closureData input)
  direct = classBelowGlobalDissipationAtOneSixtyFourth
    input (Bony.highLow b) (highLowBelowTotal input)
  ownerBound :
    Bony.highLow b
    ≤ Critical.Critical.oneSixtyFourth * Owner.dissipation environment
      + 0ℚ + 0ℚ * Owner.integralCritical environment
  ownerBound = subst
    (λ upper → Bony.highLow b ≤ upper)
    (sym (solve
      (Critical.Critical.oneSixtyFourth ∷ Owner.dissipation environment ∷ [])))
    direct

physicalCCOwnerEstimate :
  ∀ {environment} →
  PhysicalLowerThreeCriticalOwnerInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalCCOwnerEstimate {environment} input =
  Owner.admissible-owner-estimate
    Tax.CC
    (Bony.comparable b)
    Critical.Critical.oneSixtyFourth
    0ℚ 0ℚ
    ownerBound
  where
  b = Critical.budget (closureData input)
  direct = classBelowGlobalDissipationAtOneSixtyFourth
    input (Bony.comparable b) (comparableBelowTotal input)
  ownerBound :
    Bony.comparable b
    ≤ Critical.Critical.oneSixtyFourth * Owner.dissipation environment
      + 0ℚ + 0ℚ * Owner.integralCritical environment
  ownerBound = subst
    (λ upper → Bony.comparable b ≤ upper)
    (sym (solve
      (Critical.Critical.oneSixtyFourth ∷ Owner.dissipation environment ∷ [])))
    direct

lowerThreeCriticalOwnerExtractionClosed : Bool
lowerThreeCriticalOwnerExtractionClosed = true

highHighToLowNotSilentlyRelabelledTail : Bool
highHighToLowNotSilentlyRelabelledTail = true

lowerThreeCriticalOwnerExtractionClosedIsTrue :
  lowerThreeCriticalOwnerExtractionClosed ≡ true
lowerThreeCriticalOwnerExtractionClosedIsTrue = refl

highHighToLowNotSilentlyRelabelledTailIsTrue :
  highHighToLowNotSilentlyRelabelledTail ≡ true
highHighToLowNotSilentlyRelabelledTailIsTrue = refl
