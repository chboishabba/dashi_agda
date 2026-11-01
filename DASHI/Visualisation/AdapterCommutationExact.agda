module DASHI.Visualisation.AdapterCommutationExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.GraphSeriesSemanticExact as Graph
import DASHI.Visualisation.MeasureFieldAdapterExact as Adapter

------------------------------------------------------------------------
-- Source and visual transformations.  Exact commutation is checked before
-- rasterisation where semantic values remain available.

data AdapterLawStatus : Set where
  exactCommutation : AdapterLawStatus
  laxCommutation : AdapterLawStatus
  undefinedTransformation : AdapterLawStatus

sourceBarSwap : Graph.BarDatum → Graph.BarDatum
sourceBarSwap = Graph.swapBars

visualMarkSwap : Nat × Nat → Nat × Nat
visualMarkSwap = Graph.swapMarks

barSwapCommutation :
  (datum : Graph.BarDatum) →
  Graph.renderBarMarks (sourceBarSwap datum)
  ≡
  visualMarkSwap (Graph.renderBarMarks datum)
barSwapCommutation = Graph.barRelabellingEquivariant

sourceBarAggregation : Graph.BarDatum → Nat
sourceBarAggregation = Graph.aggregateBars

visualBarAggregation : Nat × Nat → Nat
visualBarAggregation (left , right) = left + right

barAggregationCommutation :
  (datum : Graph.BarDatum) →
  sourceBarAggregation datum
  ≡
  visualBarAggregation (Graph.renderBarMarks datum)
barAggregationCommutation (Graph.barDatum left right) = refl

data SourceTransformation : Set where
  swapCategories : SourceTransformation
  aggregateCategories : SourceTransformation
  alterNetworkEmbedding : SourceTransformation

data VisualTransformation : Set where
  swapRenderedMarks : VisualTransformation
  aggregateRenderedMarks : VisualTransformation
  rigidlyMoveField : VisualTransformation

adapterLaw : SourceTransformation → AdapterLawStatus
adapterLaw swapCategories = exactCommutation
adapterLaw aggregateCategories = exactCommutation
adapterLaw alterNetworkEmbedding = laxCommutation

networkEmbeddingLawIsNotExactByDefault :
  adapterLaw alterNetworkEmbedding ≡ exactCommutation → ⊥
networkEmbeddingLawIsNotExactByDefault ()

------------------------------------------------------------------------
-- Approximate/lax commutation defect.

data VisualDefect : Set where
  zeroVisualDefect : VisualDefect
  boundedVisualDefect : Nat → VisualDefect

networkEmbeddingDefect : VisualDefect
networkEmbeddingDefect = boundedVisualDefect 2

networkEmbeddingHasDeclaredDefect :
  networkEmbeddingDefect ≡ boundedVisualDefect 2
networkEmbeddingHasDeclaredDefect = refl

------------------------------------------------------------------------
-- Series and network data become measures before field generation.

data EventTime : Set where
  timeOne : EventTime
  timeTwo : EventTime
  timeThree : EventTime

record TimedEvent : Set where
  constructor timedEvent
  field
    eventTime : EventTime
    eventMass : Nat

open TimedEvent public

timedEventOne : TimedEvent
timedEventOne = timedEvent timeOne 2

timedEventTwo : TimedEvent
timedEventTwo = timedEvent timeThree 3

seriesMeasure : TimedEvent → Adapter.FiniteMeasure
seriesMeasure (timedEvent timeOne mass) =
  Adapter.finiteMeasure mass 0
seriesMeasure (timedEvent timeTwo mass) =
  Adapter.finiteMeasure mass mass
seriesMeasure (timedEvent timeThree mass) =
  Adapter.finiteMeasure 0 mass

seriesMeasureOneMass :
  Adapter.totalMeasureMass (seriesMeasure timedEventOne) ≡ 2
seriesMeasureOneMass = refl

seriesMeasureTwoMass :
  Adapter.totalMeasureMass (seriesMeasure timedEventTwo) ≡ 3
seriesMeasureTwoMass = refl

data NetworkNode : Set where
  nodeLeft : NetworkNode
  nodeRight : NetworkNode

nodeMass : NetworkNode → Nat
nodeMass nodeLeft = 4
nodeMass nodeRight = 1

networkMeasure : Adapter.FiniteMeasure
networkMeasure =
  Adapter.finiteMeasure
    (nodeMass nodeLeft)
    (nodeMass nodeRight)

networkMeasureMassIsFive :
  Adapter.totalMeasureMass networkMeasure ≡ 5
networkMeasureMassIsFive = refl

networkField : Adapter.Field2
networkField = Adapter.convolveScaled networkMeasure

networkFieldMassIsTen :
  Adapter.totalFieldMass networkField ≡ 10
networkFieldMassIsTen = refl

------------------------------------------------------------------------
-- Different non-rigid embedding choices may preserve source mass while
-- changing the generated field.

data EmbeddingChoice : Set where
  embeddingOne : EmbeddingChoice
  embeddingTwo : EmbeddingChoice

fieldFromEmbedding : EmbeddingChoice → Adapter.Field2
fieldFromEmbedding embeddingOne = Adapter.field2 8 2
fieldFromEmbedding embeddingTwo = Adapter.field2 5 5

embeddingOneMass :
  Adapter.totalFieldMass (fieldFromEmbedding embeddingOne) ≡ 10
embeddingOneMass = refl

embeddingTwoMass :
  Adapter.totalFieldMass (fieldFromEmbedding embeddingTwo) ≡ 10
embeddingTwoMass = refl

nonRigidEmbeddingsChangeField :
  fieldFromEmbedding embeddingOne
  ≡
  fieldFromEmbedding embeddingTwo
  →
  ⊥
nonRigidEmbeddingsChangeField ()

------------------------------------------------------------------------
-- The complete typed bridge keeps every loss-bearing stage explicit.

data BridgeStage : Set where
  sourceObjectStage : BridgeStage
  graphSpecificationStage : BridgeStage
  finiteMeasureStage : BridgeStage
  smoothedFieldStage : BridgeStage
  affineSliceStage : BridgeStage
  colourImageStage : BridgeStage

nextBridgeStage : BridgeStage → BridgeStage
nextBridgeStage sourceObjectStage = graphSpecificationStage
nextBridgeStage graphSpecificationStage = finiteMeasureStage
nextBridgeStage finiteMeasureStage = smoothedFieldStage
nextBridgeStage smoothedFieldStage = affineSliceStage
nextBridgeStage affineSliceStage = colourImageStage
nextBridgeStage colourImageStage = colourImageStage

bridgeReachesImageInFiveSteps :
  nextBridgeStage
    (nextBridgeStage
      (nextBridgeStage
        (nextBridgeStage
          (nextBridgeStage sourceObjectStage))))
  ≡
  colourImageStage
bridgeReachesImageInFiveSteps = refl

record AdapterCommutationBoundary : Set where
  constructor adapterCommutationBoundary
  field
    everyDataAdapterIsStrictTotalFunctor : Bool
    everyDataAdapterIsStrictTotalFunctorIsFalse :
      everyDataAdapterIsStrictTotalFunctor ≡ false

    graphIsomorphismMakesEveryGeneratedFieldIdentical : Bool
    graphIsomorphismMakesEveryGeneratedFieldIdenticalIsFalse :
      graphIsomorphismMakesEveryGeneratedFieldIdentical ≡ false

    equalFieldMassImpliesEqualFieldGeometry : Bool
    equalFieldMassImpliesEqualFieldGeometryIsFalse :
      equalFieldMassImpliesEqualFieldGeometry ≡ false

    rasterPixelEqualityIsRequiredForSemanticBarCommutation : Bool
    rasterPixelEqualityIsRequiredForSemanticBarCommutationIsFalse :
      rasterPixelEqualityIsRequiredForSemanticBarCommutation ≡ false

open AdapterCommutationBoundary public

canonicalAdapterCommutationBoundary : AdapterCommutationBoundary
canonicalAdapterCommutationBoundary =
  adapterCommutationBoundary
    false refl
    false refl
    false refl
    false refl
