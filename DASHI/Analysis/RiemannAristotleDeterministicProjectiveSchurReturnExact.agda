module DASHI.Analysis.RiemannAristotleDeterministicProjectiveSchurReturnExact where

------------------------------------------------------------------------
-- BIDI RETURN: DETERMINISTIC PROJECTIVE SCHUR ELIMINATION
--
-- The newest supplied Zeta23Bridge tree imports
-- `LiteralWeilDeterministicProjectiveSchur` from the aggregate root, and the
-- supplied session reports
--
--   lake build Zeta23Bridge
--
-- successful (8883 jobs).  Therefore the previously source-only Lean Schur
-- compiler is now part of a reported kernel-checked aggregate build.
--
-- Its mathematical content remains:
--
--   D_cluster = D_off + D_Gamma + D_pole
--
-- on three short tapers (prime projective defect = 0), and under deterministic
-- nuisance rank two,
--
--   elim2 D_pole D_Gamma D_cluster
--     = elim2 D_pole D_Gamma D_off.
--
-- This Agda file records provenance/status only.  The Lean proof terms are not
-- transported into Agda.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record DeterministicProjectiveSchurReturn : Set where
  constructor deterministic-projective-schur-return
  field
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true

    machineCheckedInLeanForThisReturn : Bool
    machineCheckedInLeanForThisReturnIsTrue :
      machineCheckedInLeanForThisReturn ≡ true

    aggregateLeanBuildJobsReported : String

    transportedIntoAgda : Bool
    transportedIntoAgdaIsFalse : transportedIntoAgda ≡ false

    primeProjectiveDebtInHighOrdinateLane : Bool
    primeProjectiveDebtInHighOrdinateLaneIsFalse :
      primeProjectiveDebtInHighOrdinateLane ≡ false

    gammaResidualDebtAfterSchur : Bool
    gammaResidualDebtAfterSchurIsFalse : gammaResidualDebtAfterSchur ≡ false
    poleResidualDebtAfterSchur : Bool
    poleResidualDebtAfterSchurIsFalse : poleResidualDebtAfterSchur ≡ false

    deterministicNuisanceIndependenceConstructed : Bool
    deterministicNuisanceIndependenceConstructedIsFalse :
      deterministicNuisanceIndependenceConstructed ≡ false
    targetClusterSurvivalAfterDeterministicSchurConstructed : Bool
    targetClusterSurvivalAfterDeterministicSchurConstructedIsFalse :
      targetClusterSurvivalAfterDeterministicSchurConstructed ≡ false

    boundedReading : String

open DeterministicProjectiveSchurReturn public

canonicalDeterministicProjectiveSchurReturn : DeterministicProjectiveSchurReturn
canonicalDeterministicProjectiveSchurReturn =
  deterministic-projective-schur-return
    true refl
    true refl
    "8883"
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The newest supplied aggregate Lean build now kernel-checks the deterministic projective Schur compiler. Prime debt is exactly zero in the high-ordinate short-support lane and Gamma/pole are eliminated exactly once their response vectors have rank two. The remaining construction socket is still analytic: build the short three-taper family with deterministic nuisance rank two and a surviving off-line cluster margin."

record DeterministicProjectiveSchurBoundary : Set where
  constructor deterministic-projective-schur-boundary
  field
    separatePositiveGammaBudgetSufficientUniformlyNearCriticalLine : Bool
    separatePositiveGammaBudgetSufficientUniformlyNearCriticalLineIsFalse :
      separatePositiveGammaBudgetSufficientUniformlyNearCriticalLine ≡ false
    separatePositivePoleBudgetSufficientUniformlyNearCriticalLine : Bool
    separatePositivePoleBudgetSufficientUniformlyNearCriticalLineIsFalse :
      separatePositivePoleBudgetSufficientUniformlyNearCriticalLine ≡ false
    exactDeterministicEliminationPreferred : Bool
    exactDeterministicEliminationPreferredIsTrue :
      exactDeterministicEliminationPreferred ≡ true

canonicalDeterministicProjectiveSchurBoundary : DeterministicProjectiveSchurBoundary
canonicalDeterministicProjectiveSchurBoundary =
  deterministic-projective-schur-boundary false refl false refl true refl
