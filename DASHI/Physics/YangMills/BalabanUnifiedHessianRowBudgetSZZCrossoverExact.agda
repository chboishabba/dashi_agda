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
-- Suppose the SAME local Hessian row budget rho_n carried by the unified
-- polymer norm obeys
--
--   rho_(n+1) <= (17/32) rho_n + E 2^{-n}.
--
-- The exact Round66 recurrence gives a closed upper majorant M_n.  At a
-- Balaban/SZZ crossover depth N it is enough to check
--
--   0 < K_W(u_*) - M_N.
--
-- The finite row-sum theorem gives Hess R_N[v,v] <= rho_N ||v||^2, and
-- rho_N <= M_N.  Antitonicity of the SZZ margin in both inverse coupling u and
-- Hessian cost rho transports positivity from the target pair (u_*,M_N) to the
-- actual running effective action.
--
-- This does NOT solve active-window overlap.  It removes a separate terminal
-- Hessian estimate once an overlap depth exists.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter
import DASHI.Physics.YangMills.BalabanFiniteHessianRowSumQuadraticBoundExact as Row
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross

record UnifiedHessianRowRGControl (Index : Set) : Set₁ where
  field
    rowDataAt : Nat → Row.FiniteSymmetricHessianRowBudget Index
    recurrence : Iter.SeventeenThirtySecondRGRecurrence
    recurrenceTracksRowBudget : ∀ n →
      Iter.K recurrence n ≡ Row.rowBudget (rowDataAt n)
open UnifiedHessianRowRGControl public

rowBudgetAtMostRGMajorant :
  ∀ {Index} (control : UnifiedHessianRowRGControl Index) n →
  Row.rowBudget (rowDataAt control n) ≤ Iter.majorant (recurrence control) n
rowBudgetAtMostRGMajorant control n =
  subst
    (λ left → left ≤ Iter.majorant (recurrence control) n)
    (recurrenceTracksRowBudget control n)
    (Iter.majorantDominates (recurrence control) n)

perturbedMarginAntitoneInRemainder :
  ∀ rank u {rhoSmall rhoLarge} →
  rhoSmall ≤ rhoLarge →
  Cross.perturbedSZZCurvatureMargin rank u rhoLarge
  ≤ Cross.perturbedSZZCurvatureMargin rank u rhoSmall
perturbedMarginAntitoneInRemainder rank u rhoSmallBelowLarge =
  let
    negOrder : - rhoLarge ≤ - rhoSmall
    negOrder = ℚP.neg-mono-≤ rhoSmallBelowLarge

    translated :
      Cross.szzWilsonCurvatureMargin rank u + (- rhoLarge)
      ≤ Cross.szzWilsonCurvatureMargin rank u + (- rhoSmall)
    translated = ℚP.+-monoˡ-≤ (Cross.szzWilsonCurvatureMargin rank u) negOrder
  in
  subst
    (λ left →
      left ≤ Cross.perturbedSZZCurvatureMargin rank u rhoSmall)
    (ℚRing.solve-∀ (Cross.szzWilsonCurvatureMargin rank u) rhoLarge)
    (subst
      (λ right →
        Cross.szzWilsonCurvatureMargin rank u + (- rhoLarge) ≤ right)
      (ℚRing.solve-∀ (Cross.szzWilsonCurvatureMargin rank u) rhoSmall)
      translated)

record UnifiedHessianSZZCrossover
    (Index : Set)
    (rank : Cross.RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (bounds : Flow.UniformBetaEnclosure trajectory) : Set₁ where
  field
    hessianControl : UnifiedHessianRowRGControl Index
    crossover : Cross.CrossoverTarget trajectory bounds

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

    moveU :
      Cross.perturbedSZZCurvatureMargin
        rank (Cross.targetInverseCoupling (crossover dataSet)) rhoUpper
      ≤ Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rhoUpper
    moveU = Cross.perturbedSZZMarginAntitone rank
      (Cross.crossoverInverseCouplingAtOrBelowTarget (crossover dataSet))

    moveRho :
      Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rhoUpper
      ≤ Cross.perturbedSZZCurvatureMargin
        rank (Flow.inverseCoupling trajectory depth) rho
    moveRho = perturbedMarginAntitoneInRemainder
      rank (Flow.inverseCoupling trajectory depth)
      (rowBudgetAtMostRGMajorant (hessianControl dataSet) depth)
  in
  ℚP.<-≤-trans start (ℚP.≤-trans moveU moveRho)

unifiedHessianRowRGToSZZCrossoverLevel : ProofLevel
unifiedHessianRowRGToSZZCrossoverLevel = machineChecked

physicalUnifiedHessianSZZCrossoverLevel : ProofLevel
physicalUnifiedHessianSZZCrossoverLevel = conditional
