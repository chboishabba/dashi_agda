module DASHI.Physics.Foundations.CausalCodingCosmologyBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Forward-decodable adaptive coding.

data SourceSymbol : Set where
  sourceZero : SourceSymbol
  sourceOne : SourceSymbol

data Bit : Set where
  bitZero : Bit
  bitOne : Bit

data SharedSideInformation : Set where
  canonicalSideInformation : SharedSideInformation

data DecodedHistory : Set where
  emptyHistory : DecodedHistory
  oneDecodedZero : DecodedHistory
  oneDecodedOne : DecodedHistory

data CodingContext : Set where
  initialContext : CodingContext
  afterZeroContext : CodingContext
  afterOneContext : CodingContext

contextFromPast : DecodedHistory → SharedSideInformation → CodingContext
contextFromPast emptyHistory canonicalSideInformation = initialContext
contextFromPast oneDecodedZero canonicalSideInformation = afterZeroContext
contextFromPast oneDecodedOne canonicalSideInformation = afterOneContext

initialContextUsesNoFutureSymbol :
  contextFromPast emptyHistory canonicalSideInformation ≡ initialContext
initialContextUsesNoFutureSymbol = refl

record SourcePair : Set where
  constructor sourcePair
  field
    firstSource : SourceSymbol
    secondSource : SourceSymbol

open SourcePair public

record BitPair : Set where
  constructor bitPair
  field
    firstBit : Bit
    secondBit : Bit

open BitPair public

encodeSymbol : SourceSymbol → Bit
encodeSymbol sourceZero = bitZero
encodeSymbol sourceOne = bitOne

offlineEncoder : SourcePair → BitPair
offlineEncoder pair =
  bitPair
    (encodeSymbol (firstSource pair))
    (encodeSymbol (secondSource pair))

decodeFirst : BitPair → SourceSymbol
decodeFirst (bitPair bitZero later) = sourceZero
decodeFirst (bitPair bitOne later) = sourceOne

decodeSecond : BitPair → DecodedHistory → SourceSymbol
decodeSecond (bitPair earlier bitZero) history = sourceZero
decodeSecond (bitPair earlier bitOne) history = sourceOne

canonicalSourcePair : SourcePair
canonicalSourcePair = sourcePair sourceOne sourceZero

firstSymbolDecodesFromFirstBit :
  decodeFirst (offlineEncoder canonicalSourcePair) ≡ sourceOne
firstSymbolDecodesFromFirstBit = refl

secondSymbolDecodesAfterHistoryIsAvailable :
  decodeSecond
    (offlineEncoder canonicalSourcePair)
    oneDecodedOne
  ≡
  sourceZero
secondSymbolDecodesAfterHistoryIsAvailable = refl

------------------------------------------------------------------------
-- Global code selection and causal decoding are different dependencies.

data CompleteCodeConstraint : Set where
  globallyAdmissibleCode : CompleteCodeConstraint

data CausalInfluenceClaim : Set where
  forwardInfluenceOnly : CausalInfluenceClaim
  backwardInfluenceClaimed : CausalInfluenceClaim

codeSelectionInfluence : CompleteCodeConstraint → CausalInfluenceClaim
codeSelectionInfluence globallyAdmissibleCode = forwardInfluenceOnly

globalAdmissibilityDoesNotCreateBackwardInfluence :
  codeSelectionInfluence globallyAdmissibleCode ≡ forwardInfluenceOnly
globalAdmissibilityDoesNotCreateBackwardInfluence = refl

------------------------------------------------------------------------
-- Bitstreams, physical initial states, boundary data, and observations are
-- separate types.

data PhysicalInitialState : Set where
  earlyStateA : PhysicalInitialState
  earlyStateB : PhysicalInitialState

data BoundaryData : Set where
  cauchyBoundaryData : BoundaryData
  partialNullBoundaryData : BoundaryData

data CMBObservation : Set where
  sameObservedSky : CMBObservation
  differentObservedSky : CMBObservation

observeCMB : PhysicalInitialState → CMBObservation
observeCMB earlyStateA = sameObservedSky
observeCMB earlyStateB = sameObservedSky

cmbObservationIsManyToOne :
  observeCMB earlyStateA ≡ observeCMB earlyStateB
cmbObservationIsManyToOne = refl

data LawSyntax : Set where
  cosmologicalLawSyntax : LawSyntax

data VisibleHistory : Set where
  observerPastLightConeHistory : VisibleHistory

record CosmologicalCodingDiagram : Set where
  constructor cosmologicalCodingDiagram
  field
    lawPayload : LawSyntax
    initialPayload : PhysicalInitialState
    checkpointObservation : CMBObservation
    visibleReconstruction : VisibleHistory

open CosmologicalCodingDiagram public

canonicalCosmologicalCodingDiagram : CosmologicalCodingDiagram
canonicalCosmologicalCodingDiagram =
  cosmologicalCodingDiagram
    cosmologicalLawSyntax
    earlyStateA
    sameObservedSky
    observerPastLightConeHistory

------------------------------------------------------------------------
-- A statistical channel exposes partial information without becoming a global
-- reference frame or complete Cauchy payload.

data ObservationChannel : Set where
  noisyProjectedChannel : ObservationChannel
  losslessGlobalStateChannel : ObservationChannel

cmbChannel : ObservationChannel
cmbChannel = noisyProjectedChannel

cmbChannelIsProjected : cmbChannel ≡ noisyProjectedChannel
cmbChannelIsProjected = refl

record CausalCodingCosmologyBoundary : Set where
  constructor causalCodingCosmologyBoundary
  field
    cabacPerformsGlobalMDLOptimisationByItself : Bool
    cabacPerformsGlobalMDLOptimisationByItselfIsFalse :
      cabacPerformsGlobalMDLOptimisationByItself ≡ false

    offlineSourceSearchPreventsForwardDecoding : Bool
    offlineSourceSearchPreventsForwardDecodingIsFalse :
      offlineSourceSearchPreventsForwardDecoding ≡ false

    globalConsistencyImpliesRetrocausalSignalling : Bool
    globalConsistencyImpliesRetrocausalSignallingIsFalse :
      globalConsistencyImpliesRetrocausalSignalling ≡ false

    cmbIsCompleteCosmologicalBitstream : Bool
    cmbIsCompleteCosmologicalBitstreamIsFalse :
      cmbIsCompleteCosmologicalBitstream ≡ false

    lastScatteringSkyIsGlobalCauchySurface : Bool
    lastScatteringSkyIsGlobalCauchySurfaceIsFalse :
      lastScatteringSkyIsGlobalCauchySurface ≡ false

    cmbGroundsGRAndQFTAsAReferenceFrame : Bool
    cmbGroundsGRAndQFTAsAReferenceFrameIsFalse :
      cmbGroundsGRAndQFTAsAReferenceFrame ≡ false

    universeLiterallyImplementsCABAC : Bool
    universeLiterallyImplementsCABACIsFalse :
      universeLiterallyImplementsCABAC ≡ false

open CausalCodingCosmologyBoundary public

canonicalCausalCodingCosmologyBoundary : CausalCodingCosmologyBoundary
canonicalCausalCodingCosmologyBoundary =
  causalCodingCosmologyBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
