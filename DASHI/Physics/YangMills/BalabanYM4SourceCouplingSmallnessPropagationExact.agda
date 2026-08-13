module DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Bridge RG1e to the small-coupling hypothesis of Bałaban 1989 Theorem 1 in
-- the source orientation u_k=g_k^-2:
--
--      u_k = u_{k+1} + beta_{k+1}.
--
-- Nonnegative beta implies u_{k+1} <= u_k.  Hence a lower threshold for the
-- coarsest inverse coupling propagates backwards to all finer UV scales.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (suc)
open import Data.Rational.Base as ℚ using (0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

record NonnegativeBetaTrajectory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set where
  field
    betaNonnegative : ∀ step → 0ℚ ≤ Flow.beta trajectory (suc step)

open NonnegativeBetaTrajectory public

inverseCouplingNextBelowCurrent :
  ∀ {trajectory}
    (nonnegative : NonnegativeBetaTrajectory trajectory) step →
  Flow.inverseCoupling trajectory (suc step)
  ≤ Flow.inverseCoupling trajectory step
inverseCouplingNextBelowCurrent {trajectory} nonnegative step =
  let
    nextValue = Flow.inverseCoupling trajectory (suc step)
    betaValue = Flow.beta trajectory (suc step)

    withZero : nextValue + 0ℚ ≤ nextValue + betaValue
    withZero = ℚP.+-mono-≤ ℚP.≤-refl
      (betaNonnegative nonnegative step)

    addAboveBase : nextValue ≤ nextValue + betaValue
    addAboveBase =
      subst
        (λ lower → lower ≤ nextValue + betaValue)
        (ℚRing.solve-∀ nextValue)
        withZero
  in
  subst
    (λ upper → nextValue ≤ upper)
    (sym (Flow.sourceRecurrence trajectory step))
    addAboveBase

ym4SourceCouplingMonotonicityLevel : ProofLevel
ym4SourceCouplingMonotonicityLevel = machineChecked
