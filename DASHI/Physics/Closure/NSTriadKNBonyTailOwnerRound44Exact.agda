module DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact where

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
-- Round 43 extracted LH/HL/CC individually from the already-proved positive
-- four-class estimate but intentionally did not identify HH->low with the
-- duplicate-free `tail` tax owner.  This file adds exactly the missing
-- same-object seam: a physical tail production is supplied together with an
-- equality identifying it with the literal highHighToLow Bony class.
--
-- No new estimate is postulated.  Nonnegativity of the other three positive
-- classes gives HH->low <= totalInteraction, so the existing 1/64 critical
-- closure and shell-energy subcharge prove
--
--   tailProduction <= (1/64) * physicalDissipation.
--
-- Thus the fourth Bony class becomes an admissible owner with zero data and
-- critical remainders, once (and only once) the same-object identity is given.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Bony
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNLowerThreeCriticalOwnersRound43Exact as Lower

record PhysicalTailCriticalOwnerInput
    (environment : Owner.TaxEnvironment) : Set where
  field
    lowerInput : Lower.PhysicalLowerThreeCriticalOwnerInput environment
    physicalTailProduction : ℚ
    highHighToLowIsPhysicalTail :
      Bony.highHighToLow
        (Critical.budget (Lower.closureData lowerInput))
      ≡ physicalTailProduction

open PhysicalTailCriticalOwnerInput public

otherThreeNonnegative :
  ∀ {environment}
    (input : PhysicalTailCriticalOwnerInput environment) →
  0ℚ ≤
    Bony.lowHigh
      (Critical.budget (Lower.closureData (lowerInput input)))
    + Bony.highLow
      (Critical.budget (Lower.closureData (lowerInput input)))
    + Bony.comparable
      (Critical.budget (Lower.closureData (lowerInput input)))
otherThreeNonnegative input =
  L2.addNonnegative
    (L2.addNonnegative
      (Lower.lowHighNonnegative (lowerInput input))
      (Lower.highLowNonnegative (lowerInput input)))
    (Lower.comparableNonnegative (lowerInput input))

highHighToLowBelowTotal :
  ∀ {environment}
    (input : PhysicalTailCriticalOwnerInput environment) →
  Bony.highHighToLow
      (Critical.budget (Lower.closureData (lowerInput input)))
  ≤ Bony.totalInteraction
      (Critical.budget (Lower.closureData (lowerInput input)))
highHighToLowBelowTotal input =
  let
    b = Critical.budget (Lower.closureData (lowerInput input))
    rest = Bony.lowHigh b + Bony.highLow b + Bony.comparable b
    addRest :
      Bony.highHighToLow b + 0ℚ
      ≤ Bony.highHighToLow b + rest
    addRest = ℚP.+-monoʳ-≤ (Bony.highHighToLow b)
      (otherThreeNonnegative input)
    target :
      Bony.highHighToLow b + rest ≡ Bony.totalInteraction b
    target = solve
      ( Bony.lowHigh b ∷ Bony.highLow b
      ∷ Bony.comparable b ∷ Bony.highHighToLow b ∷ [])
  in
  subst
    (λ lower → lower ≤ Bony.totalInteraction b)
    (solve (Bony.highHighToLow b ∷ []))
    (subst
      (λ upper → Bony.highHighToLow b + 0ℚ ≤ upper)
      target
      addRest)

physicalTailBelowGlobalDissipationAtOneSixtyFourth :
  ∀ {environment}
    (input : PhysicalTailCriticalOwnerInput environment) →
  physicalTailProduction input
  ≤ Critical.oneSixtyFourth * Owner.dissipation environment
physicalTailBelowGlobalDissipationAtOneSixtyFourth {environment} input =
  let
    lower = lowerInput input
    hhBound = Lower.classBelowGlobalDissipationAtOneSixtyFourth
      lower
      (Bony.highHighToLow (Critical.budget (Lower.closureData lower)))
      (highHighToLowBelowTotal input)
  in
  subst
    (λ production →
      production
      ≤ Critical.oneSixtyFourth * Owner.dissipation environment)
    (highHighToLowIsPhysicalTail input)
    hhBound

physicalTailOwnerEstimate :
  ∀ {environment} →
  PhysicalTailCriticalOwnerInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalTailOwnerEstimate {environment} input =
  Owner.admissible-owner-estimate
    Tax.tail
    (physicalTailProduction input)
    Critical.oneSixtyFourth
    0ℚ
    0ℚ
    ownerBound
  where
  direct = physicalTailBelowGlobalDissipationAtOneSixtyFourth input
  ownerBound :
    physicalTailProduction input
    ≤ Critical.oneSixtyFourth * Owner.dissipation environment
      + 0ℚ
      + 0ℚ * Owner.integralCritical environment
  ownerBound =
    subst
      (λ upper → physicalTailProduction input ≤ upper)
      (sym (solve
        (Critical.oneSixtyFourth ∷ Owner.dissipation environment ∷ [])))
      direct

physicalTailOwnerIdentity :
  ∀ {environment}
    (input : PhysicalTailCriticalOwnerInput environment) →
  Owner.owner (physicalTailOwnerEstimate input) ≡ Tax.tail
physicalTailOwnerIdentity input = refl

physicalTailEtaIsOneSixtyFourth :
  ∀ {environment}
    (input : PhysicalTailCriticalOwnerInput environment) →
  Owner.eta (physicalTailOwnerEstimate input) ≡ Critical.oneSixtyFourth
physicalTailEtaIsOneSixtyFourth input = refl

bonyTailOwnerExtractionClosed : Bool
bonyTailOwnerExtractionClosed = true

bonyTailOwnerExtractionClosedIsTrue :
  bonyTailOwnerExtractionClosed ≡ true
bonyTailOwnerExtractionClosedIsTrue = refl
