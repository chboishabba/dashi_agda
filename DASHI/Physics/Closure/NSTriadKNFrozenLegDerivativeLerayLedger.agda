module DASHI.Physics.Closure.NSTriadKNFrozenLegDerivativeLerayLedger where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact frozen-leg derivative, Leray, and Sobolev-owner ledger".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original algebraic audit.
-- Uses: the literal coefficient -i P_k[(u_p dot q)u_q], the exact
-- Grafakos--Torres transpose permutation, and the repository's self-adjoint
-- Leray/helical projector laws.
-- Relationship: records which frequency owns the derivative before and after
-- each transpose.  It does not infer identical shell powers from identical
-- incidence geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao

data PhysicalLeg : Set where
  leftMode rightMode outputMode : PhysicalLeg

data ProjectorPlacement : Set where
  originalOutputProjector transposeOutputProjector : ProjectorPlacement

data DerivativeDescription : Set where
  derivativeOnLeftMode
  derivativeOnRightMode
  derivativeOnFrozenMode
  derivativeRemainsOnHighInput : DerivativeDescription

data SobolevTarget : Set where
  leftTarget rightTarget outputTarget : SobolevTarget

frozenPhysicalLeg : Tao.FrozenLeg → PhysicalLeg
frozenPhysicalLeg Tao.freezeOutput = outputMode
frozenPhysicalLeg Tao.freezeLeft = leftMode
frozenPhysicalLeg Tao.freezeRight = rightMode

sourceDerivativeOwner : Tao.FrozenLeg → PhysicalLeg
sourceDerivativeOwner Tao.freezeOutput = rightMode
sourceDerivativeOwner Tao.freezeLeft = rightMode
sourceDerivativeOwner Tao.freezeRight = rightMode

targetDerivativeDescription : Tao.FrozenLeg → DerivativeDescription
targetDerivativeDescription Tao.freezeOutput = derivativeOnRightMode
targetDerivativeDescription Tao.freezeLeft = derivativeRemainsOnHighInput
targetDerivativeDescription Tao.freezeRight = derivativeOnFrozenMode

sourceLerayLeg : Tao.FrozenLeg → PhysicalLeg
sourceLerayLeg Tao.freezeOutput = outputMode
sourceLerayLeg Tao.freezeLeft = outputMode
sourceLerayLeg Tao.freezeRight = outputMode

targetLerayLeg : Tao.FrozenLeg → PhysicalLeg
targetLerayLeg Tao.freezeOutput = outputMode
targetLerayLeg Tao.freezeLeft = leftMode
targetLerayLeg Tao.freezeRight = rightMode

holderTarget : Tao.FrozenLeg → SobolevTarget
holderTarget Tao.freezeOutput = outputTarget
holderTarget Tao.freezeLeft = leftTarget
holderTarget Tao.freezeRight = rightTarget

record FrozenLegDerivativeReceipt : Set where
  constructor receipt
  field
    outputFreezesOutput :
      frozenPhysicalLeg Tao.freezeOutput ≡ outputMode
    firstAdjointFreezesLeft :
      frozenPhysicalLeg Tao.freezeLeft ≡ leftMode
    secondAdjointFreezesRight :
      frozenPhysicalLeg Tao.freezeRight ≡ rightMode

    outputSourceDerivativeIsRight :
      sourceDerivativeOwner Tao.freezeOutput ≡ rightMode
    firstAdjointSourceDerivativeIsRight :
      sourceDerivativeOwner Tao.freezeLeft ≡ rightMode
    secondAdjointSourceDerivativeIsRight :
      sourceDerivativeOwner Tao.freezeRight ≡ rightMode

    outputTargetDerivativeRecorded :
      targetDerivativeDescription Tao.freezeOutput ≡ derivativeOnRightMode
    firstAdjointDerivativeCanRemainHigh :
      targetDerivativeDescription Tao.freezeLeft ≡ derivativeRemainsOnHighInput
    secondAdjointDerivativeIsFrozenLowLeg :
      targetDerivativeDescription Tao.freezeRight ≡ derivativeOnFrozenMode

    originalProjectorAlwaysAtK :
      sourceLerayLeg Tao.freezeOutput ≡ outputMode
    firstAdjointTargetProjectorAtP :
      targetLerayLeg Tao.freezeLeft ≡ leftMode
    secondAdjointTargetProjectorAtQ :
      targetLerayLeg Tao.freezeRight ≡ rightMode

    outputHolderIsOutput :
      holderTarget Tao.freezeOutput ≡ outputTarget
    firstHolderIsLeft :
      holderTarget Tao.freezeLeft ≡ leftTarget
    secondHolderIsRight :
      holderTarget Tao.freezeRight ≡ rightTarget

open FrozenLegDerivativeReceipt public

frozenLegDerivativeReceipt : FrozenLegDerivativeReceipt
frozenLegDerivativeReceipt =
  receipt refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Exact analytic obligations attached to the ledger.
------------------------------------------------------------------------

record FrozenLegDerivativeTransportCutset : Set₁ where
  field
    outputIncompressibilityRelocation : Set
    outputOrderedSwapRelocation : Set

    firstTransposeVectorFormula : Set
    firstTransposeTargetProjectionFormula : Set
    firstTransposeHighDerivativeControlledByTailOrCommutator : Set

    secondTransposeVectorFormula : Set
    secondTransposeDerivativeAlreadyOnFrozenLeg : Set

    lerayOutputContraction : Set
    lerayFirstTransposeContraction : Set
    leraySecondTransposeContraction : Set

    helicalProjectionCostUniform : Set
    orbitNormalizationUniform : Set
    modeWeightTriangleInequality : Set

open FrozenLegDerivativeTransportCutset public

perLegDerivativeLedgerRepresented : Bool
perLegDerivativeLedgerRepresented = true

perLegDerivativeLedgerRepresentedIsTrue :
  perLegDerivativeLedgerRepresented ≡ true
perLegDerivativeLedgerRepresentedIsTrue = refl

allVectorTransposeDerivativeFormulasClosed : Bool
allVectorTransposeDerivativeFormulasClosed = false

allVectorTransposeDerivativeFormulasClosedIsFalse :
  allVectorTransposeDerivativeFormulasClosed ≡ false
allVectorTransposeDerivativeFormulasClosedIsFalse = refl

firstAdjointGetsPrimitiveLowDerivativeGain : Bool
firstAdjointGetsPrimitiveLowDerivativeGain = false

firstAdjointGetsPrimitiveLowDerivativeGainIsFalse :
  firstAdjointGetsPrimitiveLowDerivativeGain ≡ false
firstAdjointGetsPrimitiveLowDerivativeGainIsFalse = refl

secondAdjointDerivativeIsStructurallyLow : Bool
secondAdjointDerivativeIsStructurallyLow = true

secondAdjointDerivativeIsStructurallyLowIsTrue :
  secondAdjointDerivativeIsStructurallyLow ≡ true
secondAdjointDerivativeIsStructurallyLowIsTrue = refl
