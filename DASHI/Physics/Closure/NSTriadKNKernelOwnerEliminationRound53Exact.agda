module DASHI.Physics.Closure.NSTriadKNKernelOwnerEliminationRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Round 52 proved the exact pre-tax identity
--
--   literal = duplicate + independent
--
-- after cancellation.  This file makes the paper-level consequence explicit:
-- whenever the independent remainder vanishes, there is no independent kernel
-- production left to estimate.  In the fully cancelled case the literal kernel
-- itself is zero.  Hence a compatibility slot may remain in the nine-owner API,
-- but its physical production is exactly zero rather than assigned a positive
-- tax for bookkeeping convenience.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Physics.Closure.NSTriadKNKernelLiteralizationAuditRound51Exact as Literal
import DASHI.Physics.Closure.NSTriadKNKernelPreTaxReductionRound52Exact as Reduction

record NoIndependentKernelOwner
    (physical : Literal.PhysicalKernelConstituentInstantiation)
    (reduction : Reduction.KernelPreTaxSignedReduction physical) : Set where
  field
    independentKernelProductionIsZero :
      Reduction.independentRemainder reduction ≡ 0ℚ

open NoIndependentKernelOwner public

fullyDuplicatedKernelEliminatesIndependentOwner :
  ∀ {physical reduction} →
  Reduction.FullyDuplicatedKernel physical reduction →
  NoIndependentKernelOwner physical reduction
fullyDuplicatedKernelEliminatesIndependentOwner duplicated = record
  { independentKernelProductionIsZero =
      Reduction.fullyDuplicatedKernelLeavesNoIndependentTaxTerm duplicated
  }

fullyCancelledKernelEliminatesIndependentOwner :
  ∀ {physical reduction} →
  Reduction.FullyCancelledKernel physical reduction →
  NoIndependentKernelOwner physical reduction
fullyCancelledKernelEliminatesIndependentOwner cancelled = record
  { independentKernelProductionIsZero =
      Reduction.FullyCancelledKernel.independentRemainderIsZero cancelled
  }

fullyCancelledKernelHasZeroLiteralProduction :
  ∀ {physical reduction} →
  Reduction.FullyCancelledKernel physical reduction →
  Literal.literalKernelContribution physical ≡ 0ℚ
fullyCancelledKernelHasZeroLiteralProduction =
  Reduction.fullyCancelledKernelLiteralIsZero

kernelOwnerCanDisappearStructurally : Bool
kernelOwnerCanDisappearStructurally = true

physicalKernelLiteralizationAndReductionConstructed : Bool
physicalKernelLiteralizationAndReductionConstructed = false

kernelOwnerCanDisappearStructurallyIsTrue :
  kernelOwnerCanDisappearStructurally ≡ true
kernelOwnerCanDisappearStructurallyIsTrue = refl

physicalKernelLiteralizationAndReductionConstructedIsFalse :
  physicalKernelLiteralizationAndReductionConstructed ≡ false
physicalKernelLiteralizationAndReductionConstructedIsFalse = refl
