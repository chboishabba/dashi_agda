module DASHI.Physics.YangMills.BalabanReducedFaddeevPopovTraceLogJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact noncommutative fourth-order coefficient algebra required
-- after Round61/62 normalize the reduced ghost operator to I + X(g), with
--
--   X(g) = g X1 + g^2 X2 + g^3 X3 + g^4 X4 + O(g^5).
--
-- From log(I+X)=X-X^2/2+X^3/3-X^4/4+..., the trace coefficients through
-- degree four are
--
-- L1 = tr X1
-- L2 = tr X2 - 1/2 tr X1^2
-- L3 = tr X3 - tr(X1 X2) + 1/3 tr X1^3
-- L4 = tr X4 - tr(X1 X3) - 1/2 tr X2^2
--      + tr(X1^2 X2) - 1/4 tr X1^4.
--
-- The file does NOT assume commutativity of the Xi.  It first records the
-- ordered-word expansion and proves the compact formulas only from cyclic
-- trace identities.  The remaining physical theorem is to construct the Xi
-- from the literal background FP operator and prove that the finite matrix
-- log/determinant is represented by this jet on the selected weak-coupling
-- domain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

half third quarter : ℚ
half = + 1 / 2
third = + 1 / 3
quarter = + 1 / 4

record CyclicGhostTraceMoments4 : Set where
  field
    tr1 tr2 tr3 tr4 : ℚ
    tr11 : ℚ
    tr12 tr21 : ℚ
    tr111 : ℚ
    tr13 tr22 tr31 : ℚ
    tr112 tr121 tr211 : ℚ
    tr1111 : ℚ

    cyclic12 : tr21 ≡ tr12
    cyclic13 : tr31 ≡ tr13
    cyclic112-121 : tr121 ≡ tr112
    cyclic112-211 : tr211 ≡ tr112
open CyclicGhostTraceMoments4 public

orderedTraceLog1 : CyclicGhostTraceMoments4 → ℚ
orderedTraceLog1 moments = tr1 moments

orderedTraceLog2 : CyclicGhostTraceMoments4 → ℚ
orderedTraceLog2 moments =
  tr2 moments - half * tr11 moments

orderedTraceLog3 : CyclicGhostTraceMoments4 → ℚ
orderedTraceLog3 moments =
  tr3 moments
  - half * (tr12 moments + tr21 moments)
  + third * tr111 moments

orderedTraceLog4 : CyclicGhostTraceMoments4 → ℚ
orderedTraceLog4 moments =
  tr4 moments
  - half * (tr13 moments + tr22 moments + tr31 moments)
  + third * (tr112 moments + tr121 moments + tr211 moments)
  - quarter * tr1111 moments

cyclicTraceLog3 : CyclicGhostTraceMoments4 → ℚ
cyclicTraceLog3 moments =
  tr3 moments - tr12 moments + third * tr111 moments

cyclicTraceLog4 : CyclicGhostTraceMoments4 → ℚ
cyclicTraceLog4 moments =
  tr4 moments
  - tr13 moments
  - half * tr22 moments
  + tr112 moments
  - quarter * tr1111 moments

orderedThirdCoefficientCyclicReduction :
  ∀ moments → orderedTraceLog3 moments ≡ cyclicTraceLog3 moments
orderedThirdCoefficientCyclicReduction moments
  rewrite cyclic12 moments =
  ℚRing.solve-∀
    (tr3 moments) (tr12 moments) (tr111 moments)

orderedFourthCoefficientCyclicReduction :
  ∀ moments → orderedTraceLog4 moments ≡ cyclicTraceLog4 moments
orderedFourthCoefficientCyclicReduction moments
  rewrite cyclic13 moments
        | cyclic112-121 moments
        | cyclic112-211 moments =
  ℚRing.solve-∀
    (tr4 moments) (tr13 moments) (tr22 moments)
    (tr112 moments) (tr1111 moments)

record ReducedGhostTraceLogJet4 : Set where
  field
    moments : CyclicGhostTraceMoments4
open ReducedGhostTraceLogJet4 public

jetCoefficient1 : ReducedGhostTraceLogJet4 → ℚ
jetCoefficient1 jet = orderedTraceLog1 (moments jet)

jetCoefficient2 : ReducedGhostTraceLogJet4 → ℚ
jetCoefficient2 jet = orderedTraceLog2 (moments jet)

jetCoefficient3 : ReducedGhostTraceLogJet4 → ℚ
jetCoefficient3 jet = cyclicTraceLog3 (moments jet)

jetCoefficient4 : ReducedGhostTraceLogJet4 → ℚ
jetCoefficient4 jet = cyclicTraceLog4 (moments jet)

reducedGhostOrderedTraceLogJetLevel : ProofLevel
reducedGhostOrderedTraceLogJetLevel = machineChecked

reducedGhostCyclicTraceSimplificationLevel : ProofLevel
reducedGhostCyclicTraceSimplificationLevel = machineChecked

-- Still physical/analytic: construct the Xi and finite trace on the explicit
-- 3*(4^4-1)-dimensional reduced carrier and prove the selected matrix-log
-- convergence/determinant identity.
literalReducedGhostTraceMomentsLevel : ProofLevel
literalReducedGhostTraceMomentsLevel = conditional

literalReducedGhostFiniteLogDetIdentificationLevel : ProofLevel
literalReducedGhostFiniteLogDetIdentificationLevel = conditional
