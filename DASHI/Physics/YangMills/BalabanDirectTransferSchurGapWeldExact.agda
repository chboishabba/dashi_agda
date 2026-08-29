module DASHI.Physics.YangMills.BalabanDirectTransferSchurGapWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Volker Bach, Jürg Fröhlich and Israel Michael Sigal,
-- "Renormalization Group Analysis of Spectral Problems in Quantum Field
-- Theory", Advances in Mathematics 137 (1998), 205--298.
-- DOI: 10.1006/aima.1998.1733.
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- The Round60 Schur/Feshbach inequality was intentionally operator-neutral.
-- The direct-transfer programme needs the stronger SAME-OBJECT package:
--
--   literal transfer intertwiner
--   + gap functional evaluated on those exact fine/coarse transfer maps
--   + split Schur/remainder estimate for those exact gap values.
--
-- This module supplies that weld.  It does not assert that the physical
-- Bałaban block map satisfies the package; that remains the source-facing
-- analytic theorem.  What is eliminated is the possibility of proving a
-- Schur inequality for unrelated scalars and silently relabelling it as the
-- Lüscher transfer gap.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact as Transfer
import DASHI.Physics.YangMills.BalabanP33EffectiveSchurGapStepExact as Schur
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback

record DirectTransferSchurGapStep (Fine Coarse : Set) : Set₁ where
  field
    transfer : Transfer.TransferIntertwiner Fine Coarse

    fineGapOf : (Fine → Fine) → ℚ
    coarseGapOf : (Coarse → Coarse) → ℚ

    couplingLoss : ℚ
    remainderLoss : ℚ

    schurEstimateOnNamedTransfers :
      Schur.SplitRGGapStep
        (fineGapOf (Transfer.fineTransfer transfer))
        (coarseGapOf (Transfer.coarseTransfer transfer))
        couplingLoss
        remainderLoss

open DirectTransferSchurGapStep public

namedFineTransferGap :
  ∀ {Fine Coarse} →
  DirectTransferSchurGapStep Fine Coarse → ℚ
namedFineTransferGap step =
  fineGapOf step (Transfer.fineTransfer (transfer step))

namedCoarseTransferGap :
  ∀ {Fine Coarse} →
  DirectTransferSchurGapStep Fine Coarse → ℚ
namedCoarseTransferGap step =
  coarseGapOf step (Transfer.coarseTransfer (transfer step))

namedTransferOneStepPullbackLower :
  ∀ {Fine Coarse}
    (step : DirectTransferSchurGapStep Fine Coarse) →
  Pullback.half
    * (namedCoarseTransferGap step
      - couplingLoss step
      - remainderLoss step)
  ≤ namedFineTransferGap step
namedTransferOneStepPullbackLower step =
  Schur.splitOneStepPullbackLower
    (schurEstimateOnNamedTransfers step)

------------------------------------------------------------------------
-- A useful source-facing normal form: instead of separately supplying a
-- SplitRGGapStep receipt, prove the actual scalar estimate on the gaps of the
-- named transfer maps.  The existing constructor then packages it exactly.
------------------------------------------------------------------------

directTransferSchurGapStepFromEstimate :
  ∀ {Fine Coarse}
    (transferWitness : Transfer.TransferIntertwiner Fine Coarse)
    (fineGapFunctional : (Fine → Fine) → ℚ)
    (coarseGapFunctional : (Coarse → Coarse) → ℚ)
    (coupling remainder : ℚ) →
  coarseGapFunctional (Transfer.coarseTransfer transferWitness)
    ≤ Pullback.two
      * fineGapFunctional (Transfer.fineTransfer transferWitness)
      + coupling + remainder →
  DirectTransferSchurGapStep Fine Coarse
directTransferSchurGapStepFromEstimate
    transferWitness fineGapFunctional coarseGapFunctional
    coupling remainder estimate = record
  { transfer = transferWitness
  ; fineGapOf = fineGapFunctional
  ; coarseGapOf = coarseGapFunctional
  ; couplingLoss = coupling
  ; remainderLoss = remainder
  ; schurEstimateOnNamedTransfers =
      Schur.splitStepFromCoarseEstimate
        (fineGapFunctional (Transfer.fineTransfer transferWitness))
        (coarseGapFunctional (Transfer.coarseTransfer transferWitness))
        coupling remainder estimate
  }

sameOperatorSchurWeldLevel : ProofLevel
sameOperatorSchurWeldLevel = machineChecked

literalBalabanWilsonTransferGapEstimateLevel : ProofLevel
literalBalabanWilsonTransferGapEstimateLevel = conditional

cutoffUniformSchurLossBudgetLevel : ProofLevel
cutoffUniformSchurLossBudgetLevel = conditional
