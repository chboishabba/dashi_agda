module DASHI.Physics.YangMills.BalabanP33PhysicalGapScaleInvarianceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John Cardy,
-- "Scaling and Renormalization in Statistical Physics",
-- Cambridge University Press, 1996.
-- DOI: 10.1017/CBO9781316036440.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- CONDITIONAL STRESS-TEST SOURCE, NOT A THEOREM DEPENDENCY
--
-- Lluis Eriksson,
-- "The Yang-Mills Mass Gap on the Lattice: A Conditional Synthesis",
-- ai.viXra:2602.0033, version 2.  No DOI is assigned.
--
-- Version 2 explicitly states that literal transfer-matrix compatibility is
-- false for temporally nonlocal effective actions and replaces it by the
-- conditional hypotheses (H-BAL) and (H-FACT), or a finite volume window.
-- Nothing from that paper is imported as an Agda proof.
--
-- DASHI CONTRIBUTION
--
-- Separate the easy normalization algebra from the hard dynamical RG theorem.
-- A lattice mass and lattice spacing represent one physical mass p when
--
--   m_lat = a * p.
--
-- If both lattice quantities double under one block step, the same p is
-- represented exactly at the coarse scale.  This is proved below without
-- division.  The genuinely physical producer is the simultaneous doubling law
-- for the actual transfer/Hessian construction, not this rational corollary.
--
-- The module also combines the existing split Feshbach step
--
--   m_coarse <= 2 m_fine + epsilon_B + epsilon_R
--
-- with a_coarse = 2 a_fine and proves the loss-corrected cross-product form
--
--   a_fine (m_coarse-epsilon_B-epsilon_R)
--     <= a_coarse m_fine.
--
-- This is the division-free normalized one-step statement that a physical RG
-- theorem must instantiate.  It does not assert that the actual Yang--Mills
-- effective action satisfies the doubling or remainder hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback
import DASHI.Physics.YangMills.BalabanP33EffectiveSchurGapStepExact as Effective
import DASHI.Physics.YangMills.BalabanP33CoarseFineSchurCouplingExact as Coupling

------------------------------------------------------------------------
-- Lattice and physical mass are deliberately different quantities.
------------------------------------------------------------------------

record LatticeScaleState : Set where
  constructor latticeScaleState
  field
    latticeGap : ℚ
    latticeSpacing : ℚ

open LatticeScaleState public

PhysicalGapAt : LatticeScaleState → ℚ → Set
PhysicalGapAt state physicalGap =
  latticeGap state ≡ latticeSpacing state * physicalGap

record ExactDyadicScaleStep
    (fine coarse : LatticeScaleState) : Set where
  field
    gapDoubles :
      latticeGap coarse ≡ Pullback.two * latticeGap fine
    spacingDoubles :
      latticeSpacing coarse ≡ Pullback.two * latticeSpacing fine

open ExactDyadicScaleStep public

physicalGapPreservedByExactDyadicStep :
  ∀ {fine coarse physicalGap} →
  ExactDyadicScaleStep fine coarse →
  PhysicalGapAt fine physicalGap →
  PhysicalGapAt coarse physicalGap
physicalGapPreservedByExactDyadicStep
    {fine} {coarse} {physicalGap} step finePhysical
  rewrite gapDoubles step
        | spacingDoubles step
        | finePhysical =
  ℚRing.solve []

physicalRatioCrossProductInvariant :
  ∀ {fine coarse} →
  ExactDyadicScaleStep fine coarse →
  latticeGap coarse * latticeSpacing fine
  ≡ latticeGap fine * latticeSpacing coarse
physicalRatioCrossProductInvariant {fine} {coarse} step
  rewrite gapDoubles step | spacingDoubles step =
  ℚRing.solve []

------------------------------------------------------------------------
-- Exact finite-depth dyadic cascade.
------------------------------------------------------------------------

dyadicScale : LatticeScaleState → LatticeScaleState
dyadicScale state =
  latticeScaleState
    (Pullback.two * latticeGap state)
    (Pullback.two * latticeSpacing state)

dyadicScaleStep : ∀ state → ExactDyadicScaleStep state (dyadicScale state)
dyadicScaleStep state = record
  { gapDoubles = refl
  ; spacingDoubles = refl
  }

iterateDyadicScale : Nat → LatticeScaleState → LatticeScaleState
iterateDyadicScale zero state = state
iterateDyadicScale (suc depth) state =
  iterateDyadicScale depth (dyadicScale state)

physicalGapAtEveryDyadicDepth :
  ∀ depth state physicalGap →
  PhysicalGapAt state physicalGap →
  PhysicalGapAt (iterateDyadicScale depth state) physicalGap
physicalGapAtEveryDyadicDepth zero state physicalGap relation = relation
physicalGapAtEveryDyadicDepth (suc depth) state physicalGap relation =
  physicalGapAtEveryDyadicDepth
    depth
    (dyadicScale state)
    physicalGap
    (physicalGapPreservedByExactDyadicStep
      (dyadicScaleStep state) relation)

------------------------------------------------------------------------
-- Loss-corrected normalized Feshbach step.
------------------------------------------------------------------------

record PhysicalSplitRGStep
    (fine coarse : LatticeScaleState)
    (couplingLoss remainderLoss : ℚ) : Set where
  field
    splitGapStep :
      Effective.SplitRGGapStep
        (latticeGap fine)
        (latticeGap coarse)
        couplingLoss remainderLoss

    coarseSpacingDoubles :
      latticeSpacing coarse
      ≡ Pullback.two * latticeSpacing fine

    fineSpacingNonnegative :
      0ℚ ≤ latticeSpacing fine

open PhysicalSplitRGStep public

splitGapAfterLossBelowTwiceFine :
  ∀ {fine coarse couplingLoss remainderLoss} →
  Effective.SplitRGGapStep fine coarse couplingLoss remainderLoss →
  coarse - couplingLoss - remainderLoss
  ≤ Pullback.two * fine
splitGapAfterLossBelowTwiceFine
    {fine} {coarse} {couplingLoss} {remainderLoss} split =
  let
    shifted :
      coarse - (couplingLoss + remainderLoss)
      ≤ (Pullback.two * fine + couplingLoss + remainderLoss)
        - (couplingLoss + remainderLoss)
    shifted =
      Pullback.subtractRightMonotone
        (couplingLoss + remainderLoss)
        (Effective.coarseControlledByFineWithSplitLoss split)
  in
  subst
    (λ lower → lower ≤ Pullback.two * fine)
    (ℚRing.solve-∀ coarse couplingLoss remainderLoss)
    (subst
      (λ upper →
        coarse - (couplingLoss + remainderLoss) ≤ upper)
      (ℚRing.solve-∀ fine couplingLoss remainderLoss)
      shifted)

lossCorrectedPhysicalCrossProduct :
  ∀ {fine coarse couplingLoss remainderLoss} →
  PhysicalSplitRGStep fine coarse couplingLoss remainderLoss →
  latticeSpacing fine
    * (latticeGap coarse - couplingLoss - remainderLoss)
  ≤ latticeSpacing coarse * latticeGap fine
lossCorrectedPhysicalCrossProduct
    {fine} {coarse} {couplingLoss} {remainderLoss} physicalStep =
  let
    unscaled :
      latticeGap coarse - couplingLoss - remainderLoss
      ≤ Pullback.two * latticeGap fine
    unscaled =
      splitGapAfterLossBelowTwiceFine
        (splitGapStep physicalStep)

    scaled :
      latticeSpacing fine
        * (latticeGap coarse - couplingLoss - remainderLoss)
      ≤ latticeSpacing fine
        * (Pullback.two * latticeGap fine)
    scaled =
      Coupling.scaleMonotone
        (latticeSpacing fine)
        (fineSpacingNonnegative physicalStep)
        unscaled

    normalized :
      latticeSpacing fine
        * (latticeGap coarse - couplingLoss - remainderLoss)
      ≤ (Pullback.two * latticeSpacing fine) * latticeGap fine
    normalized =
      subst
        (λ upper →
          latticeSpacing fine
            * (latticeGap coarse - couplingLoss - remainderLoss)
          ≤ upper)
        (ℚRing.solve-∀
          (latticeSpacing fine) (latticeGap fine))
        scaled
  in
  subst
    (λ coarseSpacing →
      latticeSpacing fine
        * (latticeGap coarse - couplingLoss - remainderLoss)
      ≤ coarseSpacing * latticeGap fine)
    (sym (coarseSpacingDoubles physicalStep))
    normalized

physicalGapScaleInvarianceAlgebraLevel : ProofLevel
physicalGapScaleInvarianceAlgebraLevel = machineChecked

lossCorrectedPhysicalCrossProductLevel : ProofLevel
lossCorrectedPhysicalCrossProductLevel = machineChecked

physicalTransferMatrixDyadicCompatibilityLevel : ProofLevel
physicalTransferMatrixDyadicCompatibilityLevel = conditional

physicalUniformFluctuationInverseLocalityLevel : ProofLevel
physicalUniformFluctuationInverseLocalityLevel = conditional

physicalUniformCoarseFineCouplingLevel : ProofLevel
physicalUniformCoarseFineCouplingLevel = conditional
