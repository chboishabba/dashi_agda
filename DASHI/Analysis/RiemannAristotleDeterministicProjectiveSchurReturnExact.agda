module DASHI.Analysis.RiemannAristotleDeterministicProjectiveSchurReturnExact where

------------------------------------------------------------------------
-- BIDI RETURN: USE THREE-TAPER SCHUR ON DETERMINISTIC PROJECTIVE NUISANCES
--
-- Backward requirement:
--
-- An off-line horizontal displacement may be arbitrarily small.  Therefore a
-- uniform contradiction cannot rely only on separate positive O(r^2) Gamma and
-- pole budgets whose coefficients need not vanish with that displacement.
--
-- Forward infrastructure:
--
-- The Lean bridge already owns exact multi-taper Gram--Schmidt elimination and
-- the coordinatewise short-taper identity
--
--   D_cluster = D_off + D_Gamma + D_pole
--
-- with the prime projective defect exactly zero at high ordinate.
--
-- New Lean source owner:
--
--   LiteralWeilDeterministicProjectiveSchur.lean
--
-- vectorizes three short tapers and, provided the deterministic pole and Gamma
-- response vectors are independent, proves exactly
--
--   elim2 D_pole D_Gamma D_cluster
--     = elim2 D_pole D_Gamma D_off.
--
-- Thus Gamma and pole can in principle be removed with ZERO residual debt.  The
-- remaining analytic construction socket is a three-taper family for which:
--
--   * D_pole != 0;
--   * perp(D_pole,D_Gamma) != 0;
--   * the projected off-line cluster survives with a quantitative margin.
--
-- The source is not machine-checked in this return and is not transported as an
-- Agda proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record DeterministicProjectiveSchurReturn : Set where
  constructor deterministic-projective-schur-return
  field
    sourceImplementedInLean : Bool
    sourceImplementedInLeanIsTrue : sourceImplementedInLean ≡ true
    machineCheckedInLeanForThisReturn : Bool
    machineCheckedInLeanForThisReturnIsFalse :
      machineCheckedInLeanForThisReturn ≡ false
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
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The highest-leverage use of the three-taper Schur machinery is now deterministic: eliminate the projective pole and Gamma response vectors exactly. In the high-ordinate short-support lane prime is already zero, so after this Schur step the only residual carrier is the signed off-ordinate zero fibre. What remains is to construct a three-taper family with deterministic nuisance rank two and surviving off-line cluster response."

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
