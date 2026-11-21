module DASHI.Physics.YangMills.YMClayE1TimeKResidualCylinderWaveTransportExact where

------------------------------------------------------------------------
-- P0 original E1/Wilson source: (Euclidean time t, RG stage k)
-- indexed CUTOFF-DEPENDENT cylinder with all residuals retained.
--
-- Reuses the ALREADY ORIGINAL #1444 owners:
-- YMClayE1VariableCutoffCylinderLimitExact.ActualVariableCutoffCylinderFamily
--   (Configuration : Nat -> Set, Measure : Nat -> Set)
-- DASHI.Core.MultiscaleMDL.ResidualCodec / split / join / join-split.
--
-- There is NO fixed fictitious coarse C2 time as an infinite-time
-- continuum clock, NO new Gibbs/Wilson action and NO new convergence
-- theorem. The continuum is E1's selected continuumExpectation on
-- the SAME changing-cutoff source. The translation is supplied by
-- the caller and must be identified with original OS1/R332 Euclidean
-- covariance action before physical Yang--Mills promotion.
--
-- Finite ternary sign/zero wave chart is already separately
-- constructed in WaveAlgorithmLift; no symbolic phase is identified
-- here with a physical Wilson-loop insertion by fiat.
--
-- SOURCE-WRITTEN; Agda kernel and physical E1 sources unchecked.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Physics.YangMills.YMClayE1VariableCutoffCylinderLimitExact as E1

module _
    (tower : MDL.MultiscaleCarrier)
    (codec : MDL.ResidualCodec tower)
    {Measure : Nat → Set}
    {Observable Scalar : Set}
    (realization : E1.CylinderRealization
      (MDL.Carrier tower) Observable Scalar)
    (laws : E1.SelectedScalarConvergence Scalar)
    (original : E1.ActualVariableCutoffCylinderFamily
      (MDL.Carrier tower) Measure Observable Scalar
      realization laws)
    (timeTranslate : Observable → Nat → Observable)
  where

  -- k and t are independent; the ORIGINAL physical E1 source is at
  -- cutoff k and its configuration is never projected away.
  timeKOriginalCylinder :
    (t k : Nat) (word : Observable) →
    MDL.Carrier tower k → Scalar
  timeKOriginalCylinder t k word fine =
    E1.realization realization k (timeTranslate word t) fine

  -- EXACT finite wave/refinement-side path independence:
  -- first split original source state into coarse+residual, then
  -- reconstruct it, then evaluate the SAME physical cylinder.
  -- The result equals original direct evaluation at that cutoff.
  timeKOriginalCylinderRetainsResidual :
    ∀ t k word (fine : MDL.Carrier tower (suc k)) →
    timeKOriginalCylinder t (suc k) word
      (MDL.join codec (MDL.split codec fine))
    ≡ timeKOriginalCylinder t (suc k) word fine
  timeKOriginalCylinderRetainsResidual t k word fine =
    cong (timeKOriginalCylinder t (suc k) word)
      (MDL.join-split codec fine)

  -- Existing original E1 concrete n-dependent PHYSICAL Wilson
  -- expectation, not a new abstract measure nor bare-coarse source.
  timeKOriginalWilsonExpectation : Nat → Nat → Observable → Scalar
  timeKOriginalWilsonExpectation t k word =
    E1.finiteExpectation original k (timeTranslate word t)

  timeKOriginalContinuumExpectation : Nat → Observable → Scalar
  timeKOriginalContinuumExpectation t word =
    E1.continuumExpectation original (timeTranslate word t)

  -- BIDI finite -> continuum arrow: the ORIGINAL E1 convergence
  -- producer is simply applied to the time-translated SAME cylinder.
  -- This does not prove the physical source field is inhabited.
  timeKOriginalFiniteToContinuum :
    ∀ t word →
    E1.Converges laws
      (λ k → timeKOriginalWilsonExpectation t k word)
      (timeKOriginalContinuumExpectation t word)
  timeKOriginalFiniteToContinuum t word =
    E1.originalWilsonConverges original (timeTranslate word t)

  -- k ranges over the EXACT original E1 Nat cutoff family,
  -- including cutoff zero. The residual split/join statement is
  -- stated only at successor stages (suc k). Therefore no unjustified
  -- tail-stability property of arbitrary Converges was assumed.
