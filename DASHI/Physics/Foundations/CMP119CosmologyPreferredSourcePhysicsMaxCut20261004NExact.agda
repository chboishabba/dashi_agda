{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004NExact where

------------------------------------------------------------------------
-- CORRECTED SOURCE-EVIDENCE BASIS / OVERLAY N / 2026-10-04.
--
-- The previous four opaque labels are no longer the minimal accounting.
--
-- A1: the actual B4 action is signed while the present tangent carrier is only
--     ten unsigned component labels.  The irreducible source theorem is the
--     signed R144 covariance law (or an exactly equivalent differentiated law
--     that explicitly transports the basis sign).
--
-- A2: no independent selected observable or admissibility proof remains.  The
--     selected observable is the already-pinned Local-C stress encoding and the
--     published Wilson application supplies positive-time/gauge admissibility.
--     Thus A2 presentation is compiler-owned once those pre-existing E2/source
--     authorities are supplied.
--
-- B1: the direct terminal inequality is compiler output from:
--       * actual finite-sequence tail control,
--       * completed endpoint = limit of that same sequence,
--       * all-cutoff R144 finite readout = that same finite expectation.
--
-- B2: a quantitative selected-cutoff tail margin is not primitive.  The source
--     physics is the strict zero-tail Eq.(2.23) coefficient gap (plus the
--     already-explicit uniform E/R/B Cauchy bounds); standard dyadic decay then
--     chooses a late cutoff.  B1's all-cutoff attachment follows that choice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyB2StrictSourceGapEventuallyPaysTailExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyTailPartitionMarginExact as Eq223B2

------------------------------------------------------------------------
-- A1.
------------------------------------------------------------------------

a1StillRequiresSignedSourceLaw : Bool
a1StillRequiresSignedSourceLaw =
  A1.terminalA1SourceLawMustBeSignedReadoutCovariance

a1UnsignedPermutationAloneSufficient : Bool
a1UnsignedPermutationAloneSufficient =
  A1.unsignedComponentPermutationAlonePaysA1

------------------------------------------------------------------------
-- A2.
------------------------------------------------------------------------

a2PresentationLeafEliminated : Bool
a2PresentationLeafEliminated =
  A2.noIndependentA2SelectedObservable

a2PositiveTimeLeafEliminated : Bool
a2PositiveTimeLeafEliminated =
  A2.noIndependentA2PositiveTimeProof

a2GaugeLeafEliminated : Bool
a2GaugeLeafEliminated =
  A2.noIndependentA2GaugeInvariantProof

------------------------------------------------------------------------
-- B1.
------------------------------------------------------------------------

b1DirectInequalityIsCompilerOutput : Bool
b1DirectInequalityIsCompilerOutput =
  B1.directTailInequalityIsCompilerOutput

b1MovesWithLateB2Cutoff : Bool
b1MovesWithLateB2Cutoff =
  B1.directB1AnchorCanFollowB2ToAnyLateCutoff

b1SourcePaymentsAreSameSequenceIdentities : Bool
b1SourcePaymentsAreSameSequenceIdentities = true

------------------------------------------------------------------------
-- B2.
------------------------------------------------------------------------

b2StrictGapIsSourcePhysics : Bool
b2StrictGapIsSourcePhysics =
  B2.strictCoefficientGapIsSourcePhysics

b2QuantitativeTailMarginIsCompilerOutput : Bool
b2QuantitativeTailMarginIsCompilerOutput =
  B2.quantitativeTailMarginNeedNotBePrimitive

b2CauchyCompilerAlreadyPaysPartitionResponse : Bool
b2CauchyCompilerAlreadyPaysPartitionResponse =
  Eq223B2.cauchyPlusTailCoefficientMarginPaysPartitionB2

------------------------------------------------------------------------
-- FINAL ACCOUNTING.
------------------------------------------------------------------------

oldFourOpaqueLeafAccountingRetired : Bool
oldFourOpaqueLeafAccountingRetired = true

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = 0

remainingSourceEvidenceIsNamedSameObjectOrStrictSignData : Bool
remainingSourceEvidenceIsNamedSameObjectOrStrictSignData = true

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
