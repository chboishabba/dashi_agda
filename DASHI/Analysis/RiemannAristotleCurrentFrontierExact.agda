module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- This module is intentionally small.  It exists so future workers do not
-- reconstruct the live cutset from older historical status modules.
--
-- Closed in the Lean owner:
--
--   * normalized positive-width one-selected-zero Schur admission;
--   * exact three-taper / two-selected-zero Gram-Schmidt elimination;
--   * explicit positive taper-triple construction for three strictly ordered
--     positive height moduli;
--   * small-radius target survival and positive residual norm-square;
--   * exact invariance under re-adding the two selected nuisance responses.
--
-- Returned architectural facts in Agda:
--
--   * estimates stay attached to the certified literal carrier;
--   * exact reindexing may change presentation only;
--   * exactly eliminated selected directions require no residual budget;
--   * the generic final compiler only needs a literal projected far-tail bound
--     strictly below the usable target margin.
--
-- OPEN:
--
--   A. literal projected unselected-zero tail estimate after the exact two-zero
--      quotient, using a mechanism stronger than the exhausted absolute W(t)
--      majorant;
--   B. remaining prime/Gamma contribution in the same projected coordinates
--      (short-support annihilation may kill the prime term only in the lanes
--      where its support hypotheses remain compatible with the taper family);
--   C. a single domain-level composition theorem that identifies the literal
--      far residual with A+B and supplies B_far < strictSignalMargin;
--   D. final implication into the existing unweakened RH statement.
--
-- Highest-alpha strategy note:
--
--   The next theorem should not estimate the old absolute off-ordinate mass.
--   It should expose the actual projected response of each unselected zero in
--   the certified three-taper quotient coordinates, preserve signed/projective
--   structure as long as possible, and only majorize after exact projection.
--   If a shell/height decomposition is needed, it should be performed on that
--   literal projected carrier and then reindexed exactly for summation.
--
-- Equal height-modulus degeneracy remains visible: the current 3x3 height gate
-- requires three strictly ordered positive height moduli.  No theorem here
-- removes that degeneracy or derives RH.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AristotleCurrentFrontier : Set where
  constructor aristotle-current-frontier
  field
    oneZeroEndpointClosedInLean : Bool
    oneZeroEndpointClosedInLeanIsTrue : oneZeroEndpointClosedInLean ≡ true
    inhabitedTwoZeroThreeTaperClosedInLean : Bool
    inhabitedTwoZeroThreeTaperClosedInLeanIsTrue :
      inhabitedTwoZeroThreeTaperClosedInLean ≡ true
    selectedTwoZeroResidualDebtRequired : Bool
    selectedTwoZeroResidualDebtRequiredIsFalse :
      selectedTwoZeroResidualDebtRequired ≡ false
    projectedUnselectedZeroTailClosed : Bool
    projectedUnselectedZeroTailClosedIsFalse :
      projectedUnselectedZeroTailClosed ≡ false
    projectedPrimeGammaTailClosed : Bool
    projectedPrimeGammaTailClosedIsFalse :
      projectedPrimeGammaTailClosed ≡ false
    literalFarTailCompositionClosed : Bool
    literalFarTailCompositionClosedIsFalse :
      literalFarTailCompositionClosed ≡ false
    equalHeightDegeneracyRemoved : Bool
    equalHeightDegeneracyRemovedIsFalse : equalHeightDegeneracyRemoved ≡ false
    finalRHImplicationClosed : Bool
    finalRHImplicationClosedIsFalse : finalRHImplicationClosed ≡ false
    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The finite selected-carrier algebra and inhabited two-zero/three-taper construction are closed in Lean. The highest-alpha open work is now literal projected far-tail control in the exact quotient coordinates, followed by domain composition and the final unweakened RH implication."
