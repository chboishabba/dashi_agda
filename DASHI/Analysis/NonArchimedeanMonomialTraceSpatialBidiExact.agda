module DASHI.Analysis.NonArchimedeanMonomialTraceSpatialBidiExact where

------------------------------------------------------------------------
-- MONOMIAL TRACE -> LITERAL SPATIAL TRACE BIDI
--
-- Source `SchreierDynamicalTrace.lean` owns exact formulas for its defined
-- monomial matrix and for `oddFixedPointTrace`.  Those are theorem-bearing
-- character-space objects.  They become statements about the literal spatial
-- twisted block only after the same concrete DFT/monomial matrix weld needed
-- by the spectral-circle consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data TraceConsumer : Set where
  monomialFixedPointTrace : TraceConsumer
  intermediateOddTraceVanishing : TraceConsumer
  fullCycleOddTraceExpression : TraceConsumer
  literalSpatialIntermediateTraceVanishing : TraceConsumer
  literalSpatialFullCycleTrace : TraceConsumer


data TraceProducer : Set where
  ownedMonomialMatrixTraceFormula : TraceProducer
  ownedOddFixedPointNoFixedPointTheorem : TraceProducer
  ownedFullCycleFixedPointExpression : TraceProducer
  concreteDFTMonomialSameObjectWeld : TraceProducer
  fullCycleSignedCancellationProducer : TraceProducer

traceCutset : TraceConsumer → List TraceProducer
traceCutset monomialFixedPointTrace =
  ownedMonomialMatrixTraceFormula ∷ []
traceCutset intermediateOddTraceVanishing =
  ownedOddFixedPointNoFixedPointTheorem ∷ []
traceCutset fullCycleOddTraceExpression =
  ownedFullCycleFixedPointExpression ∷ []
traceCutset literalSpatialIntermediateTraceVanishing =
  concreteDFTMonomialSameObjectWeld ∷
  ownedOddFixedPointNoFixedPointTheorem ∷
  []
traceCutset literalSpatialFullCycleTrace =
  concreteDFTMonomialSameObjectWeld ∷
  ownedFullCycleFixedPointExpression ∷
  fullCycleSignedCancellationProducer ∷
  []

record SourceTraceStatus : Set where
  constructor sourceTraceStatus
  field
    monomialTraceEqualsFixedPointSumOwned : Bool
    intermediateOddFixedPointTraceVanishesOwned : Bool
    fullCycleOddFixedPointExpressionOwned : Bool
    theoremTypeUsesLiteralTwistedDirMatrixTrace : Bool
    fullCycleOddTraceCancellationToZeroLocated : Bool
    literalSpatialTraceTransportOwned : Bool

canonicalSourceTraceStatus : SourceTraceStatus
canonicalSourceTraceStatus =
  sourceTraceStatus true true true false false false

record SharedProducerFanoutBoundary : Set where
  constructor sharedProducerFanoutBoundary
  field
    spectralCircleNeedsConcreteDFTMonomialWeld : Bool
    spatialTraceNeedsSameConcreteDFTMonomialWeld : Bool
    separateUnrelatedSpatialTraceWeldShouldBeSearched : Bool
    monomialTraceTheoremMayBeRelabelledSpatialWithoutWeld : Bool

canonicalSharedProducerFanoutBoundary : SharedProducerFanoutBoundary
canonicalSharedProducerFanoutBoundary =
  sharedProducerFanoutBoundary true true false false

traceAndSpectralCircleShareWeld :
  SharedProducerFanoutBoundary.separateUnrelatedSpatialTraceWeldShouldBeSearched
    canonicalSharedProducerFanoutBoundary
  ≡ false
traceAndSpectralCircleShareWeld = refl
