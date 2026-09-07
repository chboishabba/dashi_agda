module DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-PROVER RETURN: §37 QUARTER-PERIOD / DENSITY-WINDOW RECONCILIATION
--
-- Lean owner:
--   Zeta23Bridge/Zeta23Bridge/NearCoreQuarterPeriodDensityWindow.lean
--
-- Reproduced theorem surface reported by the incoming checked Lean tranche:
--   density_cutoff_bound_eq
--   leading_window_nonempty_iff
--   quarter_period_and_density_window
--   quarter_period_and_density_force_c_lt
--   no_window_of_density_constants
--   exists_cutoff_in_window
--   matched_densities_lt
--   exists_cutoff_in_window_of_matched_densities_width_le_four
--
-- IMPORTANT FIREWALL:
-- These analytic theorems are proof-carrying Lean results.  This Agda module
-- records their interface/provenance and the cross-prover frontier only; it does
-- not reconstruct the real-analysis proofs and therefore does not promote them
-- to Agda theorems.
------------------------------------------------------------------------

data QuarterDensityAuthority : Set where
  checkedLeanTheorem : QuarterDensityAuthority
  openAgdaTransport : QuarterDensityAuthority

record QuarterPeriodDensityWindowReturn : Set where
  constructor quarter-period-density-window-return
  field
    leanOwner : String
    reportedAggregateJobsAfterAddition : String
    authority : QuarterDensityAuthority

    machineCheckedInLean : Bool
    machineCheckedInLeanIsTrue : machineCheckedInLean ≡ true
    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    exactDensityCutoffIdentityOwnedInLean : Bool
    exactDensityCutoffIdentityOwnedInLeanIsTrue :
      exactDensityCutoffIdentityOwnedInLean ≡ true

    leadingWindowNonemptyIffOwnedInLean : Bool
    leadingWindowNonemptyIffOwnedInLeanIsTrue :
      leadingWindowNonemptyIffOwnedInLean ≡ true

    jointQuarterPeriodDensityNecessityOwnedInLean : Bool
    jointQuarterPeriodDensityNecessityOwnedInLeanIsTrue :
      jointQuarterPeriodDensityNecessityOwnedInLean ≡ true

    explicitIntegerCutoffExistenceOwnedInLean : Bool
    explicitIntegerCutoffExistenceOwnedInLeanIsTrue :
      explicitIntegerCutoffExistenceOwnedInLean ≡ true

    matchedConstantsWidthLeFourWindowOwnedInLean : Bool
    matchedConstantsWidthLeFourWindowOwnedInLeanIsTrue :
      matchedConstantsWidthLeFourWindowOwnedInLean ≡ true

    densityCutAloneProvesC_lt_piSqA : Bool
    densityCutAloneProvesC_lt_piSqAIsFalse :
      densityCutAloneProvesC_lt_piSqA ≡ false

    densityCutRefutesInverseWidthRoute : Bool
    densityCutRefutesInverseWidthRouteIsFalse :
      densityCutRefutesInverseWidthRoute ≡ false

    matchedDensityAsymptoticProvedBySection37 : Bool
    matchedDensityAsymptoticProvedBySection37IsFalse :
      matchedDensityAsymptoticProvedBySection37 ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    exactIdentityReading : String
    leadingWindowReading : String
    finiteIntegerWindowReading : String
    matchedDensityScopeReading : String
    frontierReading : String

open QuarterPeriodDensityWindowReturn public

canonicalQuarterPeriodDensityWindowReturn : QuarterPeriodDensityWindowReturn
canonicalQuarterPeriodDensityWindowReturn =
  quarter-period-density-window-return
    "Zeta23Bridge.Zeta23Bridge.NearCoreQuarterPeriodDensityWindow"
    "8896"
    checkedLeanTheorem
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "At D = pi/(3 Lambda), Lean proves the density cutoff bound is exactly (pi/3 + pi^3 A/(6c))/Lambda + (1 + pi^2 A/(2c))."
    "For c > 0, Lean proves pi/2 < pi/3 + pi^3 A/(6c) iff c < pi^2 A.  The c < pi^2 A inequality is a reconciliation consequence of the two competing window requirements, not a theorem of the density estimate by itself."
    "Lean proves an actual Nat-valued cutoff exists under c < pi^2 A for every sufficiently small positive width; this is stronger than comparing two continuous interval endpoints."
    "The matched-constants theorem assumes 0 < c <= A.  Section 37 does not itself prove c and A are asymptotic to log |t|/(2 pi); any such asymptotic interpretation is external motivation and must not be promoted into this return."
    "The density cut therefore converts the adaptive inverse-width regime into a constant-window compatibility question on J*Lambda; it does not close that regime."
