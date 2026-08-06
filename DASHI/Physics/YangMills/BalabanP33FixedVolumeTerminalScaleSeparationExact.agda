module DASHI.Physics.YangMills.BalabanP33FixedVolumeTerminalScaleSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
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
-- SCOPE AND PROVENANCE NOTE
--
-- The public Lean work by Lluis Eriksson on fixed-volume Combes--Thomas and
-- volume-uniform Poincare obstructions is treated only as an external stress
-- test.  It is not imported and is not cited as authority for the theorems
-- below.  The exact public chronology is recorded separately in
-- docs/yang-mills-combes-thomas-provenance.md.
--
-- DASHI CONTRIBUTION
--
-- Make the corrected Priority-3/Priority-4 boundary kernel-visible:
--
--   1. the existing 3072-coordinate Combes--Thomas theorem is fixed-volume;
--   2. the bare unscaled one-thirty-second Poincare claim is refuted by the
--      concrete even-cycle square wave;
--   3. a terminal-scale propagator bound and a fine-scale spectral floor are
--      connected only through explicit one-step RG gap inequalities and their
--      accumulated loss budget.
--
-- The terminal scalar is not independently supplied.  The Combes--Thomas data
-- already carry the literal P33 quadratic floor, so the transfer chain is
-- definitionally terminated at P33.p33PhysicalFloor = 1/32.  Positivity is not
-- accepted as a separate receipt either: the model must prove the exact budget
--
--   discountedLossBudget(losses)
--     <= discountFactor(length losses) * (1/32).
--
-- For four RG steps this is reduced to the literal arithmetic condition
--
--   loss0/2 + loss1/4 + loss2/8 + loss3/16 <= 1/512,
--
-- and the inherited floor is
--
--   1/512 - loss0/2 - loss1/4 - loss2/8 - loss3/16.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; ∣_∣; _+_; _-_; _≤_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasQuadraticEndgameExact as CT
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival
import DASHI.Physics.YangMills.BalabanP33UnscaledCyclePoincareWallExact as Wall
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

bareUniformOneThirtySecondBlocked :
  Wall.Not
    (Wall.UniformUnscaledEvenCyclePoincare Wall.oneThirtySecond)
bareUniformOneThirtySecondBlocked =
  Wall.oneThirtySecondNotUniformUnscaled

------------------------------------------------------------------------
-- Concrete four-step terminal floor and admissible loss budget.
------------------------------------------------------------------------

p33FourStepTerminalContributionExact :
  (+ 1 / 16) * P33.p33PhysicalFloor ≡ + 1 / 512
p33FourStepTerminalContributionExact = ℚRing.solve []

fourStepWeightedLoss : ℚ → ℚ → ℚ → ℚ → ℚ
fourStepWeightedLoss loss0 loss1 loss2 loss3 =
  (+ 1 / 2) * loss0
  + (+ 1 / 4) * loss1
  + (+ 1 / 8) * loss2
  + (+ 1 / 16) * loss3

p33FourStepPullbackExact : ∀ loss0 loss1 loss2 loss3 →
  Pullback.pullBackGap P33.p33PhysicalFloor
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
  ≡ (+ 1 / 512) - fourStepWeightedLoss loss0 loss1 loss2 loss3
p33FourStepPullbackExact loss0 loss1 loss2 loss3 =
  trans
    (Pullback.fourStepPullbackExact
      P33.p33PhysicalFloor loss0 loss1 loss2 loss3)
    (ℚRing.solve-∀ loss0 loss1 loss2 loss3)

fourStepDiscountedLossExact : ∀ loss0 loss1 loss2 loss3 →
  Pullback.discountedLossBudget
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
  ≡ fourStepWeightedLoss loss0 loss1 loss2 loss3
fourStepDiscountedLossExact loss0 loss1 loss2 loss3 =
  ℚRing.solve-∀ loss0 loss1 loss2 loss3

p33FourStepDiscountedTerminalExact : ∀ loss0 loss1 loss2 loss3 →
  Pullback.discountFactor
      (Pullback.listLength (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ []))
    * P33.p33PhysicalFloor
  ≡ + 1 / 512
p33FourStepDiscountedTerminalExact loss0 loss1 loss2 loss3 =
  ℚRing.solve []

FourStepPhysicalLossBudget : ℚ → ℚ → ℚ → ℚ → Set
FourStepPhysicalLossBudget loss0 loss1 loss2 loss3 =
  fourStepWeightedLoss loss0 loss1 loss2 loss3 ≤ + 1 / 512

fourStepPhysicalBudgetAdmissible : ∀ loss0 loss1 loss2 loss3 →
  FourStepPhysicalLossBudget loss0 loss1 loss2 loss3 →
  Pullback.discountedLossBudgetAdmissible
    P33.p33PhysicalFloor
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
fourStepPhysicalBudgetAdmissible
    loss0 loss1 loss2 loss3 weightedBelowTerminal =
  let
    losses = loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ []

    weightedBelowDiscountedTerminal :
      fourStepWeightedLoss loss0 loss1 loss2 loss3
      ≤ Pullback.discountFactor (Pullback.listLength losses)
          * P33.p33PhysicalFloor
    weightedBelowDiscountedTerminal =
      subst
        (λ upper →
          fourStepWeightedLoss loss0 loss1 loss2 loss3 ≤ upper)
        (sym
          (p33FourStepDiscountedTerminalExact
            loss0 loss1 loss2 loss3))
        weightedBelowTerminal
  in
  subst
    (λ lower →
      lower
      ≤ Pullback.discountFactor (Pullback.listLength losses)
          * P33.p33PhysicalFloor)
    (sym (fourStepDiscountedLossExact loss0 loss1 loss2 loss3))
    weightedBelowDiscountedTerminal

record TerminalScalePriorityThreeData
    (fineGap : ℚ)
    (losses : List ℚ)
    (hessian green : PhysicalMatrix) : Set₁ where
  field
    terminalCombesThomasData :
      CT.PhysicalQuadraticCombesThomasData hessian green

    physicalGapTransferChain :
      Pullback.GapTransferChain
        fineGap losses P33.p33PhysicalFloor

    discountedPhysicalLossBudget :
      Pullback.discountedLossBudgetAdmissible
        P33.p33PhysicalFloor losses

open TerminalScalePriorityThreeData public

terminalScaleGreenKernelDecay :
  ∀ {fineGap losses hessian green}
    (data : TerminalScalePriorityThreeData
      fineGap losses hessian green)
    target →
  ∣ green
      (Promotion.root
        (CT.quadraticGeometry (terminalCombesThomasData data)))
      target ∣
  ≤ Survival.p33InverseScale
      * Promotion.physicalWeight
          (CT.quadraticGeometry (terminalCombesThomasData data))
          target
terminalScaleGreenKernelDecay data target =
  CT.physicalGreenKernelDecayFromQuadraticCoercivity
    (terminalCombesThomasData data) target

pulledBackPhysicalFloorNonnegative :
  ∀ {fineGap losses hessian green}
    (data : TerminalScalePriorityThreeData
      fineGap losses hessian green) →
  0ℚ ≤ Pullback.pullBackGap P33.p33PhysicalFloor losses
pulledBackPhysicalFloorNonnegative {losses = losses} data =
  Pullback.admissibleBudgetImpliesPulledBackNonnegative
    P33.p33PhysicalFloor losses (discountedPhysicalLossBudget data)

fineScaleGapNonnegativeFromTerminalChain :
  ∀ {fineGap losses hessian green}
    (data : TerminalScalePriorityThreeData
      fineGap losses hessian green) →
  0ℚ ≤ fineGap
fineScaleGapNonnegativeFromTerminalChain data =
  Pullback.admissibleBudgetImpliesFineNonnegative
    (physicalGapTransferChain data)
    (discountedPhysicalLossBudget data)

terminalDecayAndFineGapFloor :
  ∀ {fineGap losses hessian green}
    (data : TerminalScalePriorityThreeData
      fineGap losses hessian green)
    target →
  (∣ green
      (Promotion.root
        (CT.quadraticGeometry (terminalCombesThomasData data)))
      target ∣
    ≤ Survival.p33InverseScale
        * Promotion.physicalWeight
            (CT.quadraticGeometry (terminalCombesThomasData data))
            target)
  × (0ℚ ≤ fineGap)
terminalDecayAndFineGapFloor data target =
  terminalScaleGreenKernelDecay data target
  , fineScaleGapNonnegativeFromTerminalChain data

fixedVolumeCombesThomasScopeLevel : ProofLevel
fixedVolumeCombesThomasScopeLevel = machineChecked

bareVolumeUniformPromotionLevel : ProofLevel
bareVolumeUniformPromotionLevel = machineChecked

terminalScaleGapTransferCompositionLevel : ProofLevel
terminalScaleGapTransferCompositionLevel = machineChecked

physicalOneStepRGGapEstimateLevel : ProofLevel
physicalOneStepRGGapEstimateLevel = conditional
