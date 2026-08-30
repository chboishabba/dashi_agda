module DASHI.Physics.Closure.NSTriadKNFiniteTimeConcentrationTerminalVanishingRound278Exact where

------------------------------------------------------------------------
-- ROUND278 / FINITE-TIME CONCENTRATION -> TERMINAL VANISHING GEOMETRY
--
-- This is the branch on which ESS is naturally relevant.  If the almost-
-- periodic critical element has finite terminal time T* and N(t) -> infinity
-- as t -> T*, compactness after rescaling can imply weak/local vanishing in
-- fixed physical coordinates.  To feed ESS one must upgrade that statement to
-- the precise terminal vorticity vanishing/decay class used by backward
-- uniqueness.
--
-- The upgrade is not hidden: local energy/tail control, suitable regularity,
-- and passage from velocity weak vanishing to vorticity terminal data remain
-- explicit receipts.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record FiniteTimeConcentrationTerminalVanishing {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics
    finiteTerminalTime : Set ℓ
    frequencyScaleTendsToInfinityAtTerminalTime : Set ℓ
    renormalizedOrbitPrecompact : Set ℓ

    fixedScaleVelocityWeakOrLocalVanishing : Set ℓ
    localEnergyAndTailControl : Set ℓ
    suitableRegularityUpToBackwardInterval : Set ℓ

    terminalVorticityVanishingInESSClass : Set ℓ
    essCoefficientClassAvailable : Set ℓ

open FiniteTimeConcentrationTerminalVanishing public

round278FiniteTimeConcentrationIsNaturalESSEntryBranch : Bool
round278FiniteTimeConcentrationIsNaturalESSEntryBranch = true

round278WeakVelocityVanishingAloneIsNotESSVorticityData : Bool
round278WeakVelocityVanishingAloneIsNotESSVorticityData = true

round278TerminalVanishingUpgradeClosed : Bool
round278TerminalVanishingUpgradeClosed = false

round278PackageAClosed : Bool
round278PackageAClosed = false

round278TerminalVanishingUpgradeClosedIsFalse :
  round278TerminalVanishingUpgradeClosed ≡ false
round278TerminalVanishingUpgradeClosedIsFalse = refl
