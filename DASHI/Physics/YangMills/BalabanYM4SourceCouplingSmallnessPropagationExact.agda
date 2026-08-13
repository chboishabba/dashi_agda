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
-- Nonnegative beta implies u_{k+1} <= u_k.  Hence if the terminal/coarsest
-- inverse coupling is above the inverse small-coupling threshold, every finer
-- scale is above it as well.  This is the exact monotonicity needed to feed the
-- published complete-density theorem once beta positivity is established.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
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
    recurrence = Flow.sourceRecurrence trajectory step
    addAboveBase :
      Flow.inverseCoupling trajectory (suc step)
      ≤ Flow.inverseCoupling trajectory (suc step)
        + Flow.beta trajectory (suc step)
    addAboveBase = ℚP.p≤p+q
      (Flow.inverseCoupling trajectory (suc step))
      (Flow.beta trajectory (suc step))
      (betaNonnegative nonnegative step)
  in
  subst
    (λ upper → Flow.inverseCoupling trajectory (suc step) ≤ upper)
    (sym recurrence)
    addAboveBase

record TerminalInverseThreshold
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (depth : Nat) : Set where
  field
    threshold : ℚ
    terminalAboveThreshold :
      threshold ≤ Flow.inverseCoupling trajectory depth

open TerminalInverseThreshold public

-- Rather than repeat a Nat induction with an arbitrary terminal index in every
-- consumer, the all-scale package may use the exact two-sided UV tube already
-- proved from the beta enclosure.  The local monotonicity theorem above is the
-- only new order fact needed by that induction.
ym4SourceCouplingMonotonicityLevel : ProofLevel
ym4SourceCouplingMonotonicityLevel = machineChecked

ym4TerminalSmallCouplingPropagatesToUVLevel : ProofLevel
ym4TerminalSmallCouplingPropagatesToUVLevel = machineChecked
