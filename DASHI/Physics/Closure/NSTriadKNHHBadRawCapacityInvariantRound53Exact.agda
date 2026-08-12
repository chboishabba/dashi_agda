module DASHI.Physics.Closure.NSTriadKNHHBadRawCapacityInvariantRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Expose the strongest/literal HH-bad producer surface: an invariant capacity
-- for the UNNORMALIZED directional defect.  For one selected threshold delta_*,
-- a physical proof may provide
--
--   B_q <= H_q <= delta_* 2^(-q) C_*.
--
-- Exact dyadic normalization then gives
--
--   delta_*^-1 2^q B_q <= C_*,
--
-- with no alpha_q, beta_q, Green function, or recurrence mechanism exposed to
-- the final producer.  Those remain optional diagnostics.  The resulting common
-- ceiling feeds the mature selected-threshold HH-bad owner with eta = 2 C_*.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact as Factor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact as Subcharge
import DASHI.Physics.Closure.NSTriadKNHHBadNormalizedProfileRound45Exact as Profile
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected

normalizationFactor : Threshold.PositiveThreshold → Nat → ℚ
normalizationFactor parameter q =
  Threshold.thresholdInverse parameter * Sharp.dyadicScale q

normalizationFactorNonnegative :
  ∀ parameter q → 0ℚ ≤ normalizationFactor parameter q
normalizationFactorNonnegative parameter q =
  let instance
    inverseNNI = nonNegative (Threshold.thresholdInverseNonnegative parameter)
    scaleNNI = nonNegative (Scale.dyadicScaleNonnegative q)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (Threshold.thresholdInverse parameter)
        (Sharp.dyadicScale q)
  in
  ℚP.nonNegative⁻¹ (normalizationFactor parameter q)

canonicalRawCapacity :
  Threshold.PositiveThreshold → ℚ → Nat → ℚ
canonicalRawCapacity parameter ceiling q =
  Threshold.threshold parameter
  * Sharp.inverseDyadicScale q
  * ceiling

normalizedCanonicalCapacityExact :
  ∀ parameter ceiling q →
  normalizationFactor parameter q
    * canonicalRawCapacity parameter ceiling q
  ≡ ceiling
normalizedCanonicalCapacityExact parameter ceiling q =
  let
    inverse = Threshold.thresholdInverse parameter
    threshold = Threshold.threshold parameter
    dyadic = Sharp.dyadicScale q
    inverseDyadic = Sharp.inverseDyadicScale q

    regroup :
      (inverse * dyadic) * (threshold * inverseDyadic * ceiling)
      ≡ (inverse * threshold) * (inverseDyadic * dyadic) * ceiling
    regroup = solve (inverse ∷ threshold ∷ dyadic ∷ inverseDyadic ∷ ceiling ∷ [])

    cancelThreshold :
      (inverse * threshold) * (inverseDyadic * dyadic) * ceiling
      ≡ 1ℚ * (inverseDyadic * dyadic) * ceiling
    cancelThreshold =
      cong (λ product → product * (inverseDyadic * dyadic) * ceiling)
        (Threshold.inverseMeaning parameter)

    cancelDyadic :
      1ℚ * (inverseDyadic * dyadic) * ceiling
      ≡ 1ℚ * 1ℚ * ceiling
    cancelDyadic =
      cong (λ product → 1ℚ * product * ceiling)
        (Sharp.inverseDyadicReciprocal q)

    finish : 1ℚ * 1ℚ * ceiling ≡ ceiling
    finish = solve (ceiling ∷ [])
  in
  trans regroup (trans cancelThreshold (trans cancelDyadic finish))

record RawDefectCapacityInvariant : Set where
  field
    selectedThreshold : Threshold.PositiveThreshold
    defectRate capacity : Nat → ℚ
    ceiling : ℚ

    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q
    capacityNonnegative : ∀ q → 0ℚ ≤ capacity q
    ceilingNonnegative : 0ℚ ≤ ceiling

    defectBelowCapacity : ∀ q → defectRate q ≤ capacity q
    capacityBelowCanonicalRawCapacity : ∀ q →
      capacity q ≤ canonicalRawCapacity selectedThreshold ceiling q

open RawDefectCapacityInvariant public

normalizedDefect : RawDefectCapacityInvariant → Nat → ℚ
normalizedDefect physical q =
  normalizationFactor (selectedThreshold physical) q
  * defectRate physical q

normalizedDefectBelowCeiling :
  (physical : RawDefectCapacityInvariant) →
  ∀ q → normalizedDefect physical q ≤ ceiling physical
normalizedDefectBelowCeiling physical q =
  let
    factor = normalizationFactor (selectedThreshold physical) q
    factorNN = normalizationFactorNonnegative (selectedThreshold physical) q

    defectToCapacity :
      factor * defectRate physical q ≤ factor * capacity physical q
    defectToCapacity =
      let instance factorNNI = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor (defectBelowCapacity physical q)

    capacityToCanonical :
      factor * capacity physical q
      ≤ factor
        * canonicalRawCapacity
            (selectedThreshold physical) (ceiling physical) q
    capacityToCanonical =
      let instance factorNNI = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor
        (capacityBelowCanonicalRawCapacity physical q)

    combined :
      normalizedDefect physical q
      ≤ factor
        * canonicalRawCapacity
            (selectedThreshold physical) (ceiling physical) q
    combined = ℚP.≤-trans defectToCapacity capacityToCanonical
  in
  subst
    (normalizedDefect physical q ≤_)
    (normalizedCanonicalCapacityExact
      (selectedThreshold physical) (ceiling physical) q)
    combined

record RawCapacityLiteralGainBridge
    (effectiveViscosity : ℚ)
    (physical : RawDefectCapacityInvariant) : Set where
  field
    density : Nat → ℚ
    densityNonnegative : ∀ shell → 0ℚ ≤ density shell
    cells : ∀ shell →
      List (Gain.RestrictedGainDensityCell
        effectiveViscosity (density shell) shell)

    normalizedGainBelowNormalizedDefect : ∀ shell →
      Factor.scaleFreeDensityCoefficient (density shell) shell
      ≤ normalizedDefect physical shell

open RawCapacityLiteralGainBridge public

rawCapacityToSelectedProfile :
  ∀ {effectiveViscosity physical} →
  RawCapacityLiteralGainBridge effectiveViscosity physical →
  Selected.SelectedThresholdHHBadNormalizedProfile effectiveViscosity
rawCapacityToSelectedProfile {physical = physical} bridge = record
  { selectedThreshold = selectedThreshold physical
  ; density = density bridge
  ; densityNonnegative = densityNonnegative bridge
  ; cells = cells bridge
  ; selectedProfileCeiling = ceiling physical
  ; selectedProfileCeilingNonnegative = ceilingNonnegative physical
  ; normalizedCoefficientBelowSelectedCeiling = λ shell →
      ℚP.≤-trans
        (normalizedGainBelowNormalizedDefect bridge shell)
        (normalizedDefectBelowCeiling physical shell)
  }

record PhysicalRawCapacityHHBadOwnerInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ)
    (physical : RawDefectCapacityInvariant) : Set where
  field
    bridge : RawCapacityLiteralGainBridge effectiveViscosity physical
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    unmaskedChargeBelowPhysicalDissipation : ∀ shell →
      Subcharge.sumCellUnmaskedViscousCharge
        effectiveViscosity shell
        (Gain.cells
          (Factor.asRound39InverseShellCertificate
            (Profile.canonicalOneDerivativeDensityAtShell
              (Selected.selectedThresholdToRound45Profile
                (rawCapacityToSelectedProfile bridge))
              shell)))
      ≤ Owner.dissipation environment

open PhysicalRawCapacityHHBadOwnerInput public

asPhysicalSelectedThresholdProfile :
  ∀ {environment effectiveViscosity physical} →
  PhysicalRawCapacityHHBadOwnerInput
    environment effectiveViscosity physical →
  Selected.PhysicalSelectedThresholdHHBadOwnerProfile
    environment effectiveViscosity
asPhysicalSelectedThresholdProfile input = record
  { selectedProfile = rawCapacityToSelectedProfile (bridge input)
  ; viscosityNonnegative = viscosityNonnegative input
  ; selectedUnmaskedChargeBelowPhysicalDissipation =
      unmaskedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerFromRawCapacity :
  ∀ {environment effectiveViscosity physical} →
  PhysicalRawCapacityHHBadOwnerInput
    environment effectiveViscosity physical →
  Nat → Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerFromRawCapacity input =
  Selected.physicalHHBadOwnerFromOneSelectedThreshold
    (asPhysicalSelectedThresholdProfile input)

physicalRawCapacityOwnerEtaExact :
  ∀ {environment effectiveViscosity physical}
    (input : PhysicalRawCapacityHHBadOwnerInput
      environment effectiveViscosity physical) →
  ∀ shell →
  Owner.eta (physicalHHBadOwnerFromRawCapacity input shell)
  ≡ Sharp.two * ceiling physical
physicalRawCapacityOwnerEtaExact input shell =
  Profile.physicalHHBadOwnerEtaIsTwiceProfileCeiling
    (Selected.selectedThresholdToPhysicalRound45Profile
      (asPhysicalSelectedThresholdProfile input))
    shell

rawPhysicalCapacityBypassesRecurrenceMechanism : Bool
rawPhysicalCapacityBypassesRecurrenceMechanism = true

physicalRawCapacityInvariantConstructed : Bool
physicalRawCapacityInvariantConstructed = false

rawPhysicalCapacityBypassesRecurrenceMechanismIsTrue :
  rawPhysicalCapacityBypassesRecurrenceMechanism ≡ true
rawPhysicalCapacityBypassesRecurrenceMechanismIsTrue = refl
