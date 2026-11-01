module DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ) renaming (_+_ to _+ℤ_)

import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryNineZeroFibreCountExact as Count

record NineTrits : Set where
  constructor nineTrits
  field
    interaction1 interaction2 interaction3 : SSP.SSPTrit
    appraisalA1 appraisalA2 appraisalA3 : SSP.SSPTrit
    appraisalB1 appraisalB2 appraisalB3 : SSP.SSPTrit
open NineTrits public

flattenRound : Cube.OneRoundInteractionState → NineTrits
flattenRound
  (Cube.oneRoundInteractionState
    (Cube.interactionCube i1 i2 i3)
    (Cube.appraisalFibre
      (Cube.participantAppraisal a1 a2 a3)
      (Cube.participantAppraisal b1 b2 b3))) =
  nineTrits i1 i2 i3 a1 a2 a3 b1 b2 b3

rebuildRound : NineTrits → Cube.OneRoundInteractionState
rebuildRound (nineTrits i1 i2 i3 a1 a2 a3 b1 b2 b3) =
  Cube.oneRoundInteractionState
    (Cube.interactionCube i1 i2 i3)
    (Cube.appraisalFibre
      (Cube.participantAppraisal a1 a2 a3)
      (Cube.participantAppraisal b1 b2 b3))

flattenRebuildRoundTrip : (coordinates : NineTrits) →
  flattenRound (rebuildRound coordinates) ≡ coordinates
flattenRebuildRoundTrip coordinates = refl

rebuildFlattenRoundTrip : (state : Cube.OneRoundInteractionState) →
  rebuildRound (flattenRound state) ≡ state
rebuildFlattenRoundTrip
  (Cube.oneRoundInteractionState
    (Cube.interactionCube i1 i2 i3)
    (Cube.appraisalFibre
      (Cube.participantAppraisal a1 a2 a3)
      (Cube.participantAppraisal b1 b2 b3))) = refl

tripleCoordinateSum : SSP.SSPTrit → SSP.SSPTrit → SSP.SSPTrit → ℤ
tripleCoordinateSum x y z =
  Interaction.sspInteger x +ℤ Interaction.sspInteger y +ℤ Interaction.sspInteger z

nineCoordinateSum : NineTrits → ℤ
nineCoordinateSum (nineTrits i1 i2 i3 a1 a2 a3 b1 b2 b3) =
  tripleCoordinateSum i1 i2 i3
  +ℤ tripleCoordinateSum a1 a2 a3
  +ℤ tripleCoordinateSum b1 b2 b3

base369AggregateIsNineCoordinateSum :
  (state : Cube.OneRoundInteractionState) →
  Interaction.aggregateSum state ≡ nineCoordinateSum (flattenRound state)
base369AggregateIsNineCoordinateSum
  (Cube.oneRoundInteractionState
    (Cube.interactionCube i1 i2 i3)
    (Cube.appraisalFibre
      (Cube.participantAppraisal a1 a2 a3)
      (Cube.participantAppraisal b1 b2 b3))) = refl

base369FineCountMatchesCoefficientRowTotal :
  Interaction.fineInteractionStateCount ≡ Count.sumList Count.row9
base369FineCountMatchesCoefficientRowTotal = refl

base369AggregateZeroFibreCoefficient : Nat
base369AggregateZeroFibreCoefficient = Count.aggregateZeroFibreCount

base369AggregateZeroFibreCoefficientIs3139 :
  base369AggregateZeroFibreCoefficient ≡ 3139
base369AggregateZeroFibreCoefficientIs3139 = Count.aggregateZeroFibreCountIs3139

record Base369NineCoordinateAggregateBoundary : Set where
  field
    threeSemanticBlocksAreSameCarrierAsNineLabelledTrits : Bool
    existingAggregateEqualsFlattenedNineCoordinateSum : Bool
    aggregateZeroFibreCoefficientIsSingleton : Bool
    aggregateZeroFibreCoefficientComputedExactly : Bool

canonicalBase369NineCoordinateAggregateBoundary : Base369NineCoordinateAggregateBoundary
canonicalBase369NineCoordinateAggregateBoundary = record
  { threeSemanticBlocksAreSameCarrierAsNineLabelledTrits = true
  ; existingAggregateEqualsFlattenedNineCoordinateSum = true
  ; aggregateZeroFibreCoefficientIsSingleton = false
  ; aggregateZeroFibreCoefficientComputedExactly = true
  }
