{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.BishopBernoulliScharfetterGummelBridgeExact where

------------------------------------------------------------------------
-- BISHOP-BACKED BERNOULLI WEIGHT
--
-- The repository already vendors viktorcsimma/bishop and already defines the
-- exponential as the limit of the concrete Bishop exponential power series.
-- This owner therefore does not postulate a new exponential or inverse.
--
-- The only point-local analytic payment required to form
--
--   B(psi) = psi / (exp(psi) - 1)
--
-- is a proof that exp(psi)-1 is nonzero (and, when needed, positive).  The
-- inverse itself is the canonical checked inverse from vendor/bishop/Inverse.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Sum.Base using (inj₂)

import Real as BishopReal
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact as FiniteSG

------------------------------------------------------------------------
-- Exact analytic carrier.
------------------------------------------------------------------------

bishopExp :
  Series.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
bishopExp = Series.bishopExp

bernoulliDenominator :
  Series.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
bernoulliDenominator dataSet psi =
  BishopReal._-_ (bishopExp dataSet psi) BishopReal.1ℝ

record BishopBernoulliPoint
    (dataSet : Series.BishopElementaryPowerSeriesData) : Set where
  constructor bishopBernoulliPoint
  field
    psi : BishopReal.ℝ
    denominatorNonzero :
      BishopReal._≄0 (bernoulliDenominator dataSet psi)

open BishopBernoulliPoint public

bishopBernoulliWeight :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopBernoulliPoint dataSet → BishopReal.ℝ
bishopBernoulliWeight {dataSet} point =
  BishopReal._*_
    (psi point)
    (BishopInverse._⁻¹
      (bernoulliDenominator dataSet (psi point))
      (denominatorNonzero point))

------------------------------------------------------------------------
-- The quotient is characterized by cancellation, not by an opaque label.
------------------------------------------------------------------------

bishopBernoulliCancelsDenominator :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  (point : BishopBernoulliPoint dataSet) →
  BishopReal._≃_
    (BishopReal._*_
      (bishopBernoulliWeight point)
      (bernoulliDenominator dataSet (psi point)))
    (psi point)
bishopBernoulliCancelsDenominator {dataSet} point =
  let
    denominator = bernoulliDenominator dataSet (psi point)
    inverseLaw = BishopInverse.*-inverseˡ denominator (denominatorNonzero point)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 3
      (λ p i d → (p ⊗ i) ⊗ d ⊜ p ⊗ (i ⊗ d))
      BishopP.≃-refl
      (psi point)
      (BishopInverse._⁻¹ denominator (denominatorNonzero point))
      denominator)
    (BishopP.≃-trans
      (BishopP.*-congˡ inverseLaw)
      (BishopP.*-identityʳ (psi point)))

------------------------------------------------------------------------
-- Positive-drop specialization.
--
-- Positivity is kept as a separate receipt.  This is the exact leaf that must
-- eventually be discharged from the exponential-series coefficients/tail
-- bounds at the selected physical dimensionless potential drop.
------------------------------------------------------------------------

record PositiveBishopBernoulliPoint
    (dataSet : Series.BishopElementaryPowerSeriesData) : Set where
  constructor positiveBishopBernoulliPoint
  field
    point : BishopBernoulliPoint dataSet
    psiPositive : BishopReal._<_ BishopReal.0ℝ (psi point)
    denominatorPositive :
      BishopReal._<_ BishopReal.0ℝ
        (bernoulliDenominator dataSet (psi point))

open PositiveBishopBernoulliPoint public

positiveDenominatorGivesNonzero :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  (psiValue : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ
    (bernoulliDenominator dataSet psiValue) →
  BishopReal._≄0 (bernoulliDenominator dataSet psiValue)
positiveDenominatorGivesNonzero psiValue positive = inj₂ positive

bishopBernoulliWeightPositive :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  (positive : PositiveBishopBernoulliPoint dataSet) →
  BishopReal.Positive (bishopBernoulliWeight (point positive))
bishopBernoulliWeightPositive positive =
  BishopP.posx,y⇒posx*y
    (BishopP.0<x⇒posx (psiPositive positive))
    (BishopP.0<x⇒posx
      (BishopInverse.0<x⇒0<x⁻¹
        (denominatorNonzero (point positive))
        (denominatorPositive positive)))

------------------------------------------------------------------------
-- Forward/backward SG weight pair.
--
-- No identity between B(psi) and B(-psi) is assumed here.  Each orientation
-- carries its own Bishop point and its own nonzero-denominator receipt.
------------------------------------------------------------------------

record BishopSGWeightPair
    (dataSet : Series.BishopElementaryPowerSeriesData) : Set where
  constructor bishopSGWeightPair
  field
    forwardPoint : BishopBernoulliPoint dataSet
    backwardPoint : BishopBernoulliPoint dataSet

open BishopSGWeightPair public

forwardWeight :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopSGWeightPair dataSet → BishopReal.ℝ
forwardWeight pair = bishopBernoulliWeight (forwardPoint pair)

backwardWeight :
  {dataSet : Series.BishopElementaryPowerSeriesData} →
  BishopSGWeightPair dataSet → BishopReal.ℝ
backwardWeight pair = bishopBernoulliWeight (backwardPoint pair)

------------------------------------------------------------------------
-- Demotion of the old finite calibration.
--
-- The historical Nat weights 2 and 1 remain useful as an executable regression
-- fixture, but they are no longer allowed to masquerade as analytic Bernoulli
-- values.  Promotion requires an explicit encoding and setoid-equality receipt.
------------------------------------------------------------------------

record FiniteCalibrationMatchesBishop
    (dataSet : Series.BishopElementaryPowerSeriesData)
    (pair : BishopSGWeightPair dataSet) : Set₁ where
  field
    encodeFiniteWeight : Nat → BishopReal.ℝ

    forwardFiniteMatchesBishop :
      BishopReal._≃_
        (encodeFiniteWeight
          (FiniteSG.forwardBernoulliWeight FiniteSG.unitForwardDrop))
        (forwardWeight pair)

    backwardFiniteMatchesBishop :
      BishopReal._≃_
        (encodeFiniteWeight
          (FiniteSG.backwardBernoulliWeight FiniteSG.unitForwardDrop))
        (backwardWeight pair)

open FiniteCalibrationMatchesBishop public

------------------------------------------------------------------------
-- Exact residual leaf list.
------------------------------------------------------------------------

data BishopBernoulliResidualLeaf : Set where
  ConcreteElementarySeriesData : BishopBernoulliResidualLeaf
  PositiveDropEmbedding : BishopBernoulliResidualLeaf
  ExpMinusOnePositive : BishopBernoulliResidualLeaf
  NegativeDropDenominatorNonzero : BishopBernoulliResidualLeaf
  ForwardBackwardBernoulliRelation : BishopBernoulliResidualLeaf
  ThermalVoltageNormalization : BishopBernoulliResidualLeaf
  MobilityDiffusivityPrefactor : BishopBernoulliResidualLeaf
  FiniteCalibrationEqualityReceipt : BishopBernoulliResidualLeaf

-- Firewalls:
-- vendor/bishop inverse availability != exp(psi)-1 nonzero.
-- concrete Bishop series definition != completed exponential positivity theorem.
-- Bishop Bernoulli quotient != finite Nat calibration (2,1) without an explicit
-- FiniteCalibrationMatchesBishop receipt.
-- dimensionless Bishop weight != SI Scharfetter-Gummel current without the
-- transport prefactor, geometry and physical carrier densities.
