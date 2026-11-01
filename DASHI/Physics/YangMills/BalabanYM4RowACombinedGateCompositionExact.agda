module DASHI.Physics.YangMills.BalabanYM4RowACombinedGateCompositionExact where

------------------------------------------------------------------------
-- ROW A: ONE SOURCE SMALLNESS GATE -> MASTER TWO-GATE COMPOSITION
--
-- `BalabanYM4RowAGateCompositionExact` expects a sign gate for positivity and
-- then a second contraction gate for shooting.  The preceding combined-gate
-- theorem shows both follow from
--
--                 (C + L) gamma < b
--
-- when the coupling-tube width is at most gamma.  This file packages that
-- reduction against the actual master Row-A carrier, so downstream callers no
-- longer need to supply two unrelated numerical gates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RowAGateCompositionExact as Gate
import DASHI.Physics.YangMills.BalabanYM4RowACombinedSmallCouplingGateExact as One
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic

record CombinedRowAGateData (cutoff : Nat) : Set₁ where
  field
    gaussianFloor interactionConstant couplingCap tubeWidth derivativeBound : ℚ
    coupling betaGauss betaInteraction inverseSquare : Nat → ℚ

    interactionConstantNN : 0ℚ ≤ interactionConstant
    derivativeBoundNN : 0ℚ ≤ derivativeBound
    couplingCapNN : 0ℚ ≤ couplingCap
    tubeWidthNN : 0ℚ ≤ tubeWidth
    tubeWidthBelowCouplingCap : tubeWidth ≤ couplingCap

    couplingPositive : ∀ j → 0ℚ < coupling j
    couplingBelowCap : ∀ j → coupling j ≤ couplingCap
    gaussianLower : ∀ j → gaussianFloor ≤ betaGauss j
    interactionLower : ∀ j →
      - (interactionConstant * coupling j) ≤ betaInteraction j

    inverseSquareRelation : ∀ j →
      inverseSquare j * (coupling j * coupling j) ≡ 1ℚ
    couplingMonotone : ∀ j → coupling j ≤ coupling (suc j)
    betaIsInverseSquareStep : ∀ j → j ℕ.< cutoff →
      betaGauss j + betaInteraction j
      ≡ inverseSquare j - inverseSquare (suc j)

    couplingTube : ∀ K → coupling K - coupling zero ≤ tubeWidth

    combinedSmallness :
      (interactionConstant + derivativeBound) * couplingCap < gaussianFloor

open CombinedRowAGateData public

oneGateData :
  ∀ {cutoff} → CombinedRowAGateData cutoff → One.CombinedRowASmallCouplingGate
oneGateData dataSet = record
  { One.CombinedRowASmallCouplingGate.gaussianFloor = gaussianFloor dataSet
  ; One.CombinedRowASmallCouplingGate.interactionConstant = interactionConstant dataSet
  ; One.CombinedRowASmallCouplingGate.derivativeBound = derivativeBound dataSet
  ; One.CombinedRowASmallCouplingGate.couplingCap = couplingCap dataSet
  ; One.CombinedRowASmallCouplingGate.tubeWidth = tubeWidth dataSet
  ; One.CombinedRowASmallCouplingGate.interactionConstantNonnegative =
      interactionConstantNN dataSet
  ; One.CombinedRowASmallCouplingGate.derivativeBoundNonnegative =
      derivativeBoundNN dataSet
  ; One.CombinedRowASmallCouplingGate.couplingCapNonnegative = couplingCapNN dataSet
  ; One.CombinedRowASmallCouplingGate.tubeWidthNonnegative = tubeWidthNN dataSet
  ; One.CombinedRowASmallCouplingGate.tubeWidthBelowCouplingCap =
      tubeWidthBelowCouplingCap dataSet
  ; One.CombinedRowASmallCouplingGate.combinedSmallness = combinedSmallness dataSet
  }

asMasterGateData :
  ∀ {cutoff} → CombinedRowAGateData cutoff → Gate.RowAGateData cutoff
asMasterGateData dataSet = record
  { Gate.RowAGateData.gaussianFloor = gaussianFloor dataSet
  ; Gate.RowAGateData.interactionConstant = interactionConstant dataSet
  ; Gate.RowAGateData.couplingCap = couplingCap dataSet
  ; Gate.RowAGateData.tubeWidth = tubeWidth dataSet
  ; Gate.RowAGateData.coupling = coupling dataSet
  ; Gate.RowAGateData.betaGauss = betaGauss dataSet
  ; Gate.RowAGateData.betaInteraction = betaInteraction dataSet
  ; Gate.RowAGateData.inverseSquare = inverseSquare dataSet
  ; Gate.RowAGateData.interactionConstantNN = interactionConstantNN dataSet
  ; Gate.RowAGateData.couplingCapNN = couplingCapNN dataSet
  ; Gate.RowAGateData.couplingPositive = couplingPositive dataSet
  ; Gate.RowAGateData.couplingBelowCap = couplingBelowCap dataSet
  ; Gate.RowAGateData.gaussianLower = gaussianLower dataSet
  ; Gate.RowAGateData.interactionLower = interactionLower dataSet
  ; Gate.RowAGateData.inverseSquareRelation = inverseSquareRelation dataSet
  ; Gate.RowAGateData.couplingMonotone = couplingMonotone dataSet
  ; Gate.RowAGateData.betaIsInverseSquareStep = betaIsInverseSquareStep dataSet
  ; Gate.RowAGateData.couplingTube = couplingTube dataSet
  ; Gate.RowAGateData.signGate =
      One.combinedSmallnessGivesSignGate (oneGateData dataSet)
  }

module Combined {cutoff : Nat} (dataSet : CombinedRowAGateData cutoff) where

  master : Gate.RowAGateData cutoff
  master = asMasterGateData dataSet

  open Gate.Gates master public using
    (betaMargin; betaMarginPositive; inducedFlow; cubicSumBound)

  shootingGate :
    derivativeBound dataSet * tubeWidth dataSet < betaMargin
  shootingGate =
    One.combinedSmallnessGivesShootingGate (oneGateData dataSet)

  module Tuning
    (sensitivity : Nat → ℚ)
    (sensitivityCubic : ∀ j → sensitivity j
      ≤ (Cubic.halfℚ * derivativeBound dataSet)
          * (coupling dataSet j * coupling dataSet j * coupling dataSet j))
    where

    open Gate.Gates.Tuning master
      (derivativeBound dataSet)
      (derivativeBoundNN dataSet)
      sensitivity
      sensitivityCubic
      shootingGate
      public

rowAOneSmallnessGateToMasterSignGateLevel : ProofLevel
rowAOneSmallnessGateToMasterSignGateLevel = machineChecked

rowAOneSmallnessGateToMasterShootingGateLevel : ProofLevel
rowAOneSmallnessGateToMasterShootingGateLevel = machineChecked

rowAOneSmallnessGateCompositionLevel : ProofLevel
rowAOneSmallnessGateCompositionLevel = machineChecked

-- Source-facing leaf: instantiate finite b,C,L and a literal coupling tube with
-- width <= gamma, then prove (C+L)gamma<b.  All master sign/shooting algebra is
-- constructed above on that same trajectory.
literalRowAOneSmallnessGateInstantiationLevel : ProofLevel
literalRowAOneSmallnessGateInstantiationLevel = conditional
