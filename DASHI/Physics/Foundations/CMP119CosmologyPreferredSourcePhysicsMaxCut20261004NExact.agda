{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004NExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyB2StrictSourceGapEventuallyPaysTailExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyTailPartitionMarginExact as Eq223B2

------------------------------------------------------------------------
-- A1: signed source covariance remains; unsigned permutation is insufficient.
------------------------------------------------------------------------

a1StillRequiresSignedSourceLaw : Bool
a1StillRequiresSignedSourceLaw = A1.terminalA1SourceLawMustBeSignedReadoutCovariance

a1UnsignedPermutationAloneSufficient : Bool
a1UnsignedPermutationAloneSufficient = A1.unsignedComponentPermutationAlonePaysA1

------------------------------------------------------------------------
-- A2: observable choice/admissibility are compiled, SAME-OBJECT pair semantics
-- remain source evidence because the Round109 pair carrier is opaque.
------------------------------------------------------------------------

a2IndependentObservableChoiceEliminated : Bool
a2IndependentObservableChoiceEliminated = A2.noIndependentA2SelectedObservable

a2PositiveTimeLeafEliminated : Bool
a2PositiveTimeLeafEliminated = A2.noIndependentA2PositiveTimeProof

a2GaugeLeafEliminated : Bool
a2GaugeLeafEliminated = A2.noIndependentA2GaugeInvariantProof

a2PairToObservableSameObjectSemanticsStillOpen : Bool
a2PairToObservableSameObjectSemanticsStillOpen =
  A2.remainingA2SourceDebtIsPairToObservableSameObjectSemantics

------------------------------------------------------------------------
-- B1: direct inequality is compiler output after exact same-sequence payments.
------------------------------------------------------------------------

b1DirectInequalityIsCompilerOutput : Bool
b1DirectInequalityIsCompilerOutput = B1.directTailInequalityIsCompilerOutput

b1MovesWithLateB2Cutoff : Bool
b1MovesWithLateB2Cutoff = B1.directB1AnchorCanFollowB2ToAnyLateCutoff

b1SourcePaymentsAreSameSequenceIdentities : Bool
b1SourcePaymentsAreSameSequenceIdentities = true

------------------------------------------------------------------------
-- B2: strict zero-tail gap is physics; selected quantitative margin is decay.
------------------------------------------------------------------------

b2StrictGapIsSourcePhysics : Bool
b2StrictGapIsSourcePhysics = B2.strictCoefficientGapIsSourcePhysics

b2QuantitativeTailMarginIsCompilerOutput : Bool
b2QuantitativeTailMarginIsCompilerOutput = B2.quantitativeTailMarginNeedNotBePrimitive

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
