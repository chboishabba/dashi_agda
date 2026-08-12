module DASHI.Physics.Closure.NSTriadKNHardSoftReserveRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- Round 44 reduced the nine-owner reserve to five free etas plus the fixed
-- Bony tax 1/16.  Round 45 proves two of those five coefficients have a more
-- precise type:
--
--   * HH-good is Young-soft once its physical producer exists: eta_HHg may be
--     chosen as the threshold of any positive rational split;
--   * boundary is zero-tax once its classified physical subtype limits vanish.
--
-- HH-bad is represented by its normalized profile ceiling C_*, for which the
-- canonical tax is exactly 2 C_*.
--
-- Consequently the physical reserve at any chosen HH-good split epsilon is
-- exactly
--
--   epsilon + 2 C_* + eta_Com + eta_kernel + 4/64 < 1.
--
-- This module constructs the existing Round-44 five-owner carrier and strict
-- budget from that reduced certificate.  No viscosity is assigned to boundary,
-- and no artificial positive floor is assigned to HH-good.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_ ; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact as Tail
import DASHI.Physics.Closure.NSTriadKNFiveOwnerReserveReductionRound44Exact as Five
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

record HardSoftOwnerCore
    (environment : Owner.TaxEnvironment) : Set₁ where
  field
    hhGoodSoftFamily : Soft.YoungSoftOwnerFamily environment Tax.HH-good

    hhBadEstimate : Owner.AdmissibleOwnerEstimate environment
    hhBadOwner : Owner.owner hhBadEstimate ≡ Tax.HH-bad
    hhBadProfileCeiling : ℚ
    hhBadProfileCeilingNonnegative : 0ℚ ≤ hhBadProfileCeiling
    hhBadEtaExact :
      Owner.eta hhBadEstimate ≡ Sharp.two * hhBadProfileCeiling

    comEstimate : Owner.AdmissibleOwnerEstimate environment
    comOwner : Owner.owner comEstimate ≡ Tax.Com
    comEtaNonnegative : 0ℚ ≤ Owner.eta comEstimate

    kernelEstimate : Owner.AdmissibleOwnerEstimate environment
    kernelOwner : Owner.owner kernelEstimate ≡ Tax.kernel
    kernelEtaNonnegative : 0ℚ ≤ Owner.eta kernelEstimate

    boundaryEstimate : Owner.AdmissibleOwnerEstimate environment
    boundaryOwner : Owner.owner boundaryEstimate ≡ Tax.boundary
    boundaryEtaZero : Owner.eta boundaryEstimate ≡ 0ℚ

open HardSoftOwnerCore public

hhBadEtaNonnegative :
  ∀ {environment}
    (core : HardSoftOwnerCore environment) →
  0ℚ ≤ Owner.eta (hhBadEstimate core)
hhBadEtaNonnegative core =
  let
    twoNN : 0ℚ ≤ Sharp.two
    twoNN = ℚP.nonNegative⁻¹ Sharp.two
    productNN : 0ℚ ≤ Sharp.two * hhBadProfileCeiling core
    productNN =
      let instance
        twoNNI = nonNegative twoNN
        ceilingNNI = nonNegative (hhBadProfileCeilingNonnegative core)
        productNNI =
          ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (hhBadProfileCeiling core)
      in
      ℚP.nonNegative⁻¹ (Sharp.two * hhBadProfileCeiling core)
  in
  subst (0ℚ ≤_) (sym (hhBadEtaExact core)) productNN

remainingOwnersAtSplit :
  ∀ {environment} →
  HardSoftOwnerCore environment →
  Threshold.PositiveThreshold →
  Five.FiveRemainingPhysicalOwners environment
remainingOwnersAtSplit core split = record
  { hhGoodEstimate = Soft.estimateAtSplit (hhGoodSoftFamily core) split
  ; hhBadEstimate = hhBadEstimate core
  ; comEstimate = comEstimate core
  ; kernelEstimate = kernelEstimate core
  ; boundaryEstimate = boundaryEstimate core
  ; hhGoodOwner = Soft.ownerAtSplit (hhGoodSoftFamily core) split
  ; hhBadOwner = hhBadOwner core
  ; comOwner = comOwner core
  ; kernelOwner = kernelOwner core
  ; boundaryOwner = boundaryOwner core
  }

hardSoftEtaTotal :
  ∀ {environment} →
  HardSoftOwnerCore environment →
  Threshold.PositiveThreshold → ℚ
hardSoftEtaTotal core split =
  Threshold.threshold split
  + Sharp.two * hhBadProfileCeiling core
  + Owner.eta (comEstimate core)
  + Owner.eta (kernelEstimate core)
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

fiveOwnerEtaTotalAtSplitExact :
  ∀ {environment}
    (core : HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  Five.fiveOwnerEtaTotal (remainingOwnersAtSplit core split)
  ≡ hardSoftEtaTotal core split
fiveOwnerEtaTotalAtSplitExact core split
  rewrite Soft.etaAtSplit (hhGoodSoftFamily core) split
        | hhBadEtaExact core
        | boundaryEtaZero core =
  solve
    ( Threshold.threshold split
    ∷ Sharp.two
    ∷ hhBadProfileCeiling core
    ∷ Owner.eta (comEstimate core)
    ∷ Owner.eta (kernelEstimate core)
    ∷ Critical.oneSixtyFourth
    ∷ [])

record HardSoftStrictReserveAtSplit
    {environment : Owner.TaxEnvironment}
    (core : HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) : Set where
  field
    reducedTotalStrict : hardSoftEtaTotal core split < 1ℚ
    reducedRemainingPositive :
      0ℚ < 1ℚ - hardSoftEtaTotal core split

open HardSoftStrictReserveAtSplit public

asFiveOwnerStrictReserveInput :
  ∀ {environment}
    (core : HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold) →
  HardSoftStrictReserveAtSplit core split →
  Five.FiveOwnerStrictReserveInput (remainingOwnersAtSplit core split)
asFiveOwnerStrictReserveInput core split reserve = record
  { hhGoodEtaNonnegative =
      subst
        (0ℚ ≤_)
        (sym (Soft.etaAtSplit (hhGoodSoftFamily core) split))
        (Threshold.thresholdNonnegative split)
  ; hhBadEtaNonnegative = hhBadEtaNonnegative core
  ; comEtaNonnegative = comEtaNonnegative core
  ; kernelEtaNonnegative = kernelEtaNonnegative core
  ; boundaryEtaNonnegative =
      subst (0ℚ ≤_) (sym (boundaryEtaZero core)) ℚP.≤-refl
  ; fiveOwnerTotalStrict =
      subst
        (λ total → total < 1ℚ)
        (sym (fiveOwnerEtaTotalAtSplitExact core split))
        (reducedTotalStrict reserve)
  ; fiveOwnerRemainingPositive =
      subst
        (λ total → 0ℚ < 1ℚ - total)
        (sym (fiveOwnerEtaTotalAtSplitExact core split))
        (reducedRemainingPositive reserve)
  }

strictPhysicalNineOwnerBudgetFromHardSoftReserve :
  ∀ {environment}
    (core : HardSoftOwnerCore environment)
    (split : Threshold.PositiveThreshold)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment) →
  HardSoftStrictReserveAtSplit core split →
  Owner.StrictAdmissibleOwnerBudget
    (Owner.nineOwnerList
      (Five.physicalNineOwnerEstimateFamily
        (remainingOwnersAtSplit core split) tailInput))
strictPhysicalNineOwnerBudgetFromHardSoftReserve
    core split tailInput reserve =
  Five.strictPhysicalNineOwnerBudget
    (remainingOwnersAtSplit core split)
    tailInput
    (asFiveOwnerStrictReserveInput core split reserve)

boundaryEliminatedFromViscosityReserve : Bool
boundaryEliminatedFromViscosityReserve = true

hhGoodExposedAsSoftReserveParameter : Bool
hhGoodExposedAsSoftReserveParameter = true

boundaryEliminatedFromViscosityReserveIsTrue :
  boundaryEliminatedFromViscosityReserve ≡ true
boundaryEliminatedFromViscosityReserveIsTrue = refl

hhGoodExposedAsSoftReserveParameterIsTrue :
  hhGoodExposedAsSoftReserveParameter ≡ true
hhGoodExposedAsSoftReserveParameterIsTrue = refl
