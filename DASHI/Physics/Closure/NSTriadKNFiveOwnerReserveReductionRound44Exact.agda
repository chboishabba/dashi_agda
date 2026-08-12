module DASHI.Physics.Closure.NSTriadKNFiveOwnerReserveReductionRound44Exact where

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
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 43 exposed an exact nine-owner reserve gate.  The already-proved
-- critical four-class theorem, together with Round 44's same-object tail
-- identity, makes LH, HL, CC and tail all cost exactly the same certified
-- viscosity coefficient 1/64.  Hence the nine-dimensional strict reserve no
-- longer needs to be treated as nine independent analytic unknowns.
--
-- This module constructs the literal NineOwnerEstimateFamily and proves the
-- exact carrier identity
--
--   sumEta(nine owners)
--     = eta_HHg + eta_HHb + eta_Com + eta_kernel + eta_boundary
--       + 4 * (1/64).
--
-- Therefore only five owner coefficients remain numerically free.  A strict
-- certificate for that five-owner total (including the fixed Bony tax) gives
-- the repository's existing StrictAdmissibleOwnerBudget directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNLowerThreeCriticalOwnersRound43Exact as Lower
import DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact as Tail

record FiveRemainingPhysicalOwners
    (environment : Owner.TaxEnvironment) : Set where
  field
    hhGoodEstimate : Owner.AdmissibleOwnerEstimate environment
    hhBadEstimate : Owner.AdmissibleOwnerEstimate environment
    comEstimate : Owner.AdmissibleOwnerEstimate environment
    kernelEstimate : Owner.AdmissibleOwnerEstimate environment
    boundaryEstimate : Owner.AdmissibleOwnerEstimate environment

    hhGoodOwner : Owner.owner hhGoodEstimate ≡ Tax.HH-good
    hhBadOwner : Owner.owner hhBadEstimate ≡ Tax.HH-bad
    comOwner : Owner.owner comEstimate ≡ Tax.Com
    kernelOwner : Owner.owner kernelEstimate ≡ Tax.kernel
    boundaryOwner : Owner.owner boundaryEstimate ≡ Tax.boundary

open FiveRemainingPhysicalOwners public

physicalNineOwnerEstimateFamily :
  ∀ {environment} →
  FiveRemainingPhysicalOwners environment →
  Tail.PhysicalTailCriticalOwnerInput environment →
  Owner.NineOwnerEstimateFamily environment
physicalNineOwnerEstimateFamily remaining tailInput =
  let lower = Tail.lowerInput tailInput
  in
  Owner.nine-owner-estimate-family
    (hhGoodEstimate remaining)
    (hhBadEstimate remaining)
    (Lower.physicalLHOwnerEstimate lower)
    (Lower.physicalHLOwnerEstimate lower)
    (Lower.physicalCCOwnerEstimate lower)
    (comEstimate remaining)
    (kernelEstimate remaining)
    (Tail.physicalTailOwnerEstimate tailInput)
    (boundaryEstimate remaining)
    (hhGoodOwner remaining)
    (hhBadOwner remaining)
    refl
    refl
    refl
    (comOwner remaining)
    (kernelOwner remaining)
    (Tail.physicalTailOwnerIdentity tailInput)
    (boundaryOwner remaining)

fiveOwnerEtaTotal :
  ∀ {environment} →
  FiveRemainingPhysicalOwners environment → ℚ
fiveOwnerEtaTotal remaining =
  Owner.eta (hhGoodEstimate remaining)
  + Owner.eta (hhBadEstimate remaining)
  + Owner.eta (comEstimate remaining)
  + Owner.eta (kernelEstimate remaining)
  + Owner.eta (boundaryEstimate remaining)
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

nineOwnerEtaTotalIsFiveOwnerEtaTotal :
  ∀ {environment}
    (remaining : FiveRemainingPhysicalOwners environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) →
  Owner.sumEta
    (Owner.nineOwnerList
      (physicalNineOwnerEstimateFamily remaining tailInput))
  ≡ fiveOwnerEtaTotal remaining
nineOwnerEtaTotalIsFiveOwnerEtaTotal remaining tailInput =
  solve
    ( Owner.eta (hhGoodEstimate remaining)
    ∷ Owner.eta (hhBadEstimate remaining)
    ∷ Owner.eta (comEstimate remaining)
    ∷ Owner.eta (kernelEstimate remaining)
    ∷ Owner.eta (boundaryEstimate remaining)
    ∷ Critical.oneSixtyFourth
    ∷ [])

record FiveOwnerStrictReserveInput
    {environment : Owner.TaxEnvironment}
    (remaining : FiveRemainingPhysicalOwners environment) : Set where
  field
    hhGoodEtaNonnegative : 0ℚ ≤ Owner.eta (hhGoodEstimate remaining)
    hhBadEtaNonnegative : 0ℚ ≤ Owner.eta (hhBadEstimate remaining)
    comEtaNonnegative : 0ℚ ≤ Owner.eta (comEstimate remaining)
    kernelEtaNonnegative : 0ℚ ≤ Owner.eta (kernelEstimate remaining)
    boundaryEtaNonnegative : 0ℚ ≤ Owner.eta (boundaryEstimate remaining)

    fiveOwnerTotalStrict : fiveOwnerEtaTotal remaining < 1ℚ
    fiveOwnerRemainingPositive :
      0ℚ < 1ℚ - fiveOwnerEtaTotal remaining

open FiveOwnerStrictReserveInput public

physicalNineOwnerEtasNonnegative :
  ∀ {environment}
    (remaining : FiveRemainingPhysicalOwners environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) →
  FiveOwnerStrictReserveInput remaining →
  Owner.AllEtasNonnegative
    (Owner.nineOwnerList
      (physicalNineOwnerEstimateFamily remaining tailInput))
physicalNineOwnerEtasNonnegative remaining tailInput reserve =
  Owner.allEtas∷ (hhGoodEtaNonnegative reserve)
  (Owner.allEtas∷ (hhBadEtaNonnegative reserve)
  (Owner.allEtas∷ Lower.oneSixtyFourthNonnegative
  (Owner.allEtas∷ Lower.oneSixtyFourthNonnegative
  (Owner.allEtas∷ Lower.oneSixtyFourthNonnegative
  (Owner.allEtas∷ (comEtaNonnegative reserve)
  (Owner.allEtas∷ (kernelEtaNonnegative reserve)
  (Owner.allEtas∷ Lower.oneSixtyFourthNonnegative
  (Owner.allEtas∷ (boundaryEtaNonnegative reserve)
    Owner.allEtas[])))))))))

physicalNineOwnerEtaStrict :
  ∀ {environment}
    (remaining : FiveRemainingPhysicalOwners environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) →
  FiveOwnerStrictReserveInput remaining →
  Owner.sumEta
    (Owner.nineOwnerList
      (physicalNineOwnerEstimateFamily remaining tailInput))
  < 1ℚ
physicalNineOwnerEtaStrict remaining tailInput reserve =
  subst
    (λ total → total < 1ℚ)
    (sym (nineOwnerEtaTotalIsFiveOwnerEtaTotal remaining tailInput))
    (fiveOwnerTotalStrict reserve)

strictPhysicalNineOwnerBudget :
  ∀ {environment}
    (remaining : FiveRemainingPhysicalOwners environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) →
  FiveOwnerStrictReserveInput remaining →
  Owner.StrictAdmissibleOwnerBudget
    (Owner.nineOwnerList
      (physicalNineOwnerEstimateFamily remaining tailInput))
strictPhysicalNineOwnerBudget remaining tailInput reserve =
  Owner.strict-admissible-owner-budget
    (physicalNineOwnerEtasNonnegative remaining tailInput reserve)
    (physicalNineOwnerEtaStrict remaining tailInput reserve)
    (subst
      (λ total → 0ℚ < 1ℚ - total)
      (sym (nineOwnerEtaTotalIsFiveOwnerEtaTotal remaining tailInput))
      (fiveOwnerRemainingPositive reserve))

bonyFourOwnersShareOneSixtyFourth : Bool
bonyFourOwnersShareOneSixtyFourth = true

nineOwnerGateReducedToFiveFreeEtas : Bool
nineOwnerGateReducedToFiveFreeEtas = true

bonyFourOwnersShareOneSixtyFourthIsTrue :
  bonyFourOwnersShareOneSixtyFourth ≡ true
bonyFourOwnersShareOneSixtyFourthIsTrue = refl

nineOwnerGateReducedToFiveFreeEtasIsTrue :
  nineOwnerGateReducedToFiveFreeEtas ≡ true
nineOwnerGateReducedToFiveFreeEtasIsTrue = refl
