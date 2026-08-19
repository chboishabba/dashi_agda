module DASHI.Physics.YangMills.BalabanUnifiedHessianRowBudgetSZZCrossoverExact where

------------------------------------------------------------------------
-- ROUND69: L7 LOCAL-HESSIAN RECURRENCE -> L5 SZZ CURVATURE MARGIN
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- DASHI CONTRIBUTION
--
-- This file makes the proposed L7 -> L5 collapse quantitative.  Suppose the
-- SAME local Hessian row budget rho_n carried by the unified polymer norm obeys
-- the Round66 recurrence
--
--   rho_(n+1) <= (17/32) rho_n + E 2^{-n}.
--
-- The existing exact recurrence theorem gives a closed upper majorant M_n.
-- At a Balaban/SZZ crossover depth N it is therefore enough to check
--
--   0 < K_W(u_*) - M_N,
--
-- rather than separately estimating the full Hessian quadratic form.  The
-- finite row-sum theorem supplies
--
--   Hess R_N[v,v] <= rho_N ||v||^2 <= M_N ||v||^2,
--
-- and monotonicity in both u and rho transports the positive target margin to
-- the actual running effective action.
--
-- This does NOT solve the active-window overlap problem.  It removes a separate
-- Hessian/spectral producer once an overlap depth exists.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter
import DASHI.Physics.YangMills.BalabanFiniteHessianRowSumQuadraticBoundExact as Row
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross

record UnifiedHessianRowRGControl (Index : Set) : Set₁ where
  field
    hessianAt : _
      -- eta-expanded by Agda from the following explicit type annotation
    rowDataAt : (n : Agda.Builtin.Nat.Nat) → Row.FiniteSymmetricHessianRowBudget Index

    recurrence : Iter.SeventeenThirtySecondRGRecurrence

    recurrenceTracksRowBudget : ∀ n →
      Iter.K recurrence n ≡ Row.rowBudget (rowDataAt n)

open UnifiedHessianRowRGControl public

rowBudgetAtMostRGMajorant :
  ∀ {Index} (control : UnifiedHessianRowRGControl Index) n →
  Row.rowBudget (rowDataAt control n) ≤ Iter.majorant (recurrence control) n
rowBudgetAtMostRGMajorant control n =
  let base = Iter.majorantDominates (recurrence control) n
  in Relation.Binary.PropositionalEquality.subst
    (λ left → left ≤ Iter.majorant (recurrence control) n)
    (recurrenceTracksRowBudget control n)
    base

perturbedMarginAntitoneInRemainder :
  ∀ rank u {rhoSmall rhoLarge} →
  rhoSmall ≤ rhoLarge →
  Cross.perturbedSZZCurvatureMargin rank u rhoLarge
  ≤ Cross.perturbedSZZCurvatureMargin rank u rhoSmall
perturbedMarginAntitoneInRemainder rank u rhoSmallBelowLarge =
  let
    translated = ℚP.+-monoˡ-≤
      (Cross.szzWilsonCurvatureMargin rank u - rhoLarge)
      rhoSmallBelowLarge
  in
  Relation.Binary.PropositionalEquality.subst
    (λ right →
      Cross.perturbedSZZCurvatureMargin rank u rhoLarge ≤ right)
    (Data.Rational.Tactic.RingSolver.solve-∀
      (Cross.szzWilsonCurvatureMargin rank u) rhoSmall rhoLarge)
    translated

record UnifiedHessianSZZCrossover
    (Index : Set)
    (rank : Cross.RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set₁ where
  field
    hessianControl : UnifiedHessianRowRGControl Index
    crossover : Cross.CrossoverTarget trajectory bounds

    -- Check positivity against the CLOSED recurrence majorant, not the unknown
    -- actual row budget.
    targetMarginBeatsRGHessianMajorant :
      0ℚ < Cross.perturbedSZZCurvatureMargin
        rank
        (Cross.targetInverseCoupling crossover)
        (Iter.majorant (recurrence hessianControl) (Cross.depth crossover))

open UnifiedHessianSZZCrossover public

actualCrossoverMarginPositiveFromUnifiedHessianRG :
  ∀ {Index rank trajectory bounds}
    (dataSet : UnifiedHessianSZZCrossover Index rank trajectory bounds) →
  0ℚ < Cross.perturbedSZZCurvatureMargin
    rank
    (Flow.inverseCoupling trajectory (Cross.depth (crossover dataSet)))
    (Row.rowBudget
      (rowDataAt (hessianControl dataSet) (Cross.depth (crossover dataSet))))
actualCrossoverMarginPositiveFromUnifiedHessianRG {rank = rank} {trajectory = trajectory}
    dataSet =
  let
    depth = Cross.depth (crossover dataSet)
    rho = Row.rowBudget (rowDataAt (hessianControl dataSet) depth)
    rhoUpper = Iter.majorant (recurrence (hessianControl dataSet)) depth

    start = targetMarginBeatsRGHessianMajorant dataSet

    actualUBelowTarget =
      Cross.crossoverInverseCouplingAtOrBelowTarget (crossover dataSet)

    moveU :
      Cross.perturbedSZZCurvatureMargin
        rank (Cross.targetInverseCoupling (crossover dataSet)) rhoUpper
      ≤ Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rhoUpper
    moveU = Cross.perturbedSZZMarginAntitone rank actualUBelowTarget

    rhoBelow = rowBudgetAtMostRGMajorant (hessianControl dataSet) depth

    moveRho :
      Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rhoUpper
      ≤ Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rho
    moveRho = perturbedMarginAntitoneInRemainder
      rank (Flow.inverseCoupling trajectory depth) rhoBelow
  in
  ℚP.<-≤-trans start (ℚP.≤-trans moveU moveRho)

unifiedHessianRowRGToSZZCrossoverLevel : ProofLevel
unifiedHessianRowRGToSZZCrossoverLevel = machineChecked

-- Remaining physical content has now fused: the L7 one-step norm estimate must
-- bound the local Hessian row mass in the SAME 17/32 recurrence, and the running
-- coupling must reach an SZZ-overlap target before the Balaban active window
-- closes.  No independent terminal Hessian estimate remains on this route.
physicalUnifiedHessianSZZCrossoverLevel : ProofLevel
physicalUnifiedHessianSZZCrossoverLevel = conditional
