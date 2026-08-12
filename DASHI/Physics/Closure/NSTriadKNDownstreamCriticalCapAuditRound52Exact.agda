module DASHI.Physics.Closure.NSTriadKNDownstreamCriticalCapAuditRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Audit the actual continuation interfaces before optimizing global Young
-- splits.  At the nine-owner energy step the critical remainder is literally
--
--   (sum_i B_i) X,
--
-- so owner B coefficients aggregate there.  However the later block-decay
-- bridge still represents `RecursionCoefficientStrictlyBelowOne` as an opaque
-- physical proposition; it does not yet state whether the admissible cap is on
-- each owner coefficient separately or on their sum after the majorant is
-- assembled.
--
-- Consequently Round 51's three separate global effective floors are a safe
-- conservative parameterization, not a proved sharp optimization.  A joint
-- allocation theorem should only be installed after the physical fixed-shift
-- majorant exposes the actual aggregate coefficient formula.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNNineOwnerToBlockDecayBridgeRound43Exact as Bridge
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalBlockDecayReductionExact as Block

-- This type is intentionally the repository's existing aggregate coefficient;
-- no parallel notion of "total B" is introduced.
OwnerAggregateCriticalCoefficient : Nine.NineOwnerCriticalBalance → Set
OwnerAggregateCriticalCoefficient balance =
  Nine.sumCriticalCoefficients balance ≡ Nine.sumCriticalCoefficients balance

ownerAggregateCriticalCoefficientIsLiteral :
  (balance : Nine.NineOwnerCriticalBalance) →
  OwnerAggregateCriticalCoefficient balance
ownerAggregateCriticalCoefficientIsLiteral balance = refl

ownerEnergyRemainderAggregatesBCoefficients : Bool
ownerEnergyRemainderAggregatesBCoefficients = true

blockRecursionCapShapeExposedAsArithmeticFormula : Bool
blockRecursionCapShapeExposedAsArithmeticFormula = false

individualOwnerCapsProvedByCurrentBlockBridge : Bool
individualOwnerCapsProvedByCurrentBlockBridge = false

aggregateOwnerCapProvedByCurrentBlockBridge : Bool
aggregateOwnerCapProvedByCurrentBlockBridge = false

separateGlobalFloorsAreCurrentlyConservative : Bool
separateGlobalFloorsAreCurrentlyConservative = true

ownerEnergyRemainderAggregatesBCoefficientsIsTrue :
  ownerEnergyRemainderAggregatesBCoefficients ≡ true
ownerEnergyRemainderAggregatesBCoefficientsIsTrue = refl

blockRecursionCapShapeExposedAsArithmeticFormulaIsFalse :
  blockRecursionCapShapeExposedAsArithmeticFormula ≡ false
blockRecursionCapShapeExposedAsArithmeticFormulaIsFalse = refl
