module DASHI.Culture.IntellectualReceptionStratifiedFibreOrderBidiExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / STRATIFIED FIBRE / ORDER BIDI
--
-- Cross-pollination discipline:
--
--   * collective-memory / public-legibility semantics are consumed from the
--     merged historical-governance owner;
--   * hidden transport-order nonfactorability is consumed as structural
--     precedent from the merged cubie-face holonomy analogue;
--   * PR #666's Base369 stratified-fibre/holonomy lane is inspiration only
--     while that PR remains unmerged; this module imports no #666 owner;
--   * the reception square below is a finite DASHI construction, not a claim
--     that intellectual history is literally a gauge field, Wilson loop,
--     Base369 fibre, or physical holonomy.
--
-- Source proposition
-- != reception
-- != institutionalisation
-- != later vocabulary
-- != present use
-- != recovered original meaning.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CubieFaceOrderHolonomyAnalogueExact as Holonomy
import DASHI.Governance.SexedHistoricalCollectiveThresholdNetworkExact as Collective
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy
import DASHI.Culture.WittgensteinUsePracticeSourceBridgeExact as Wittgenstein

------------------------------------------------------------------------
-- 1. Reception fibre and coarse historical strata.
------------------------------------------------------------------------

data ReceptionState : Set where
  sourceOccurrence
  interpretedReception
  institutionalReception
  interpretationAfterInstitution
  institutionAfterInterpretation
  : ReceptionState

data ReceptionStratum : Set where
  sourceStratum
  publicInterpretationStratum
  institutionalReceptionStratum
  transmittedInstitutionalStratum
  : ReceptionStratum

data ReceptionMeaningCode : Set where
  sourceMeaning
  interpretedMeaning
  institutionalMeaning
  interpretationAfterInstitutionMeaning
  institutionAfterInterpretationMeaning
  : ReceptionMeaningCode

data AttributionAuthorityCode : Set where
  sourceAuthority
  interpretiveAuthority
  institutionalAuthority
  mixedLaterAuthority
  : AttributionAuthorityCode

receptionStratum : ReceptionState → ReceptionStratum
receptionStratum sourceOccurrence = sourceStratum
receptionStratum interpretedReception = publicInterpretationStratum
receptionStratum institutionalReception = institutionalReceptionStratum
receptionStratum interpretationAfterInstitution = transmittedInstitutionalStratum
receptionStratum institutionAfterInterpretation = transmittedInstitutionalStratum

receptionMeaning : ReceptionState → ReceptionMeaningCode
receptionMeaning sourceOccurrence = sourceMeaning
receptionMeaning interpretedReception = interpretedMeaning
receptionMeaning institutionalReception = institutionalMeaning
receptionMeaning interpretationAfterInstitution = interpretationAfterInstitutionMeaning
receptionMeaning institutionAfterInterpretation = institutionAfterInterpretationMeaning

receptionAuthority : ReceptionState → AttributionAuthorityCode
receptionAuthority sourceOccurrence = sourceAuthority
receptionAuthority interpretedReception = interpretiveAuthority
receptionAuthority institutionalReception = institutionalAuthority
receptionAuthority interpretationAfterInstitution = mixedLaterAuthority
receptionAuthority institutionAfterInterpretation = mixedLaterAuthority

------------------------------------------------------------------------
-- 2. Two reception transports; order matters.
------------------------------------------------------------------------

reinterpret : ReceptionState → ReceptionState
reinterpret sourceOccurrence = interpretedReception
reinterpret institutionalReception = interpretationAfterInstitution
reinterpret state = state

institutionalise : ReceptionState → ReceptionState
institutionalise sourceOccurrence = institutionalReception
institutionalise interpretedReception = institutionAfterInterpretation
institutionalise state = state

interpretAfterInstitution : ReceptionState
interpretAfterInstitution = reinterpret (institutionalise sourceOccurrence)

institutionAfterInterpret : ReceptionState
institutionAfterInterpret = institutionalise (reinterpret sourceOccurrence)

receptionTransportOrderDiffers :
  interpretAfterInstitution ≡ institutionAfterInterpret → ⊥
receptionTransportOrderDiffers ()

orderedEndpointsShareCoarseStratum :
  receptionStratum interpretAfterInstitution
  ≡ receptionStratum institutionAfterInterpret
orderedEndpointsShareCoarseStratum = refl

orderedEndpointsDifferInMeaning :
  receptionMeaning interpretAfterInstitution
  ≡ receptionMeaning institutionAfterInterpret → ⊥
orderedEndpointsDifferInMeaning ()

------------------------------------------------------------------------
-- 3. Literal order-erasure nonfactorability inside one coarse stratum.
------------------------------------------------------------------------

data ReceptionOrder : Set where
  interpretThenInstitutionalise
  institutionaliseThenInterpret
  : ReceptionOrder

data CoarseReceptionOrderSurface : Set where
  sameTransmittedInstitutionalSurface : CoarseReceptionOrderSurface

data FineReceptionOrderEndpoint : Set where
  interpretationAfterInstitutionEndpoint
  institutionAfterInterpretationEndpoint
  : FineReceptionOrderEndpoint

coarseOrderSurface : ReceptionOrder → CoarseReceptionOrderSurface
coarseOrderSurface _ = sameTransmittedInstitutionalSurface

fineOrderEndpoint : ReceptionOrder → FineReceptionOrderEndpoint
fineOrderEndpoint interpretThenInstitutionalise = institutionAfterInterpretationEndpoint
fineOrderEndpoint institutionaliseThenInterpret = interpretationAfterInstitutionEndpoint

orderEndpointsDiffer :
  fineOrderEndpoint interpretThenInstitutionalise
  ≡ fineOrderEndpoint institutionaliseThenInterpret → ⊥
orderEndpointsDiffer ()

coarseReceptionStratumCannotRecoverTransportOrder :
  INF.FactorsThrough coarseOrderSurface fineOrderEndpoint → ⊥
coarseReceptionStratumCannotRecoverTransportOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      interpretThenInstitutionalise
      institutionaliseThenInterpret
      refl
      orderEndpointsDiffer)

------------------------------------------------------------------------
-- 4. Present vocabulary and transmitted memory remain coarser still.
------------------------------------------------------------------------

data PresentVocabularySurface : Set where sameLaterVocabulary : PresentVocabularySurface

presentVocabulary : ReceptionOrder → PresentVocabularySurface
presentVocabulary _ = sameLaterVocabulary

presentVocabularyCannotRecoverReceptionOrder :
  INF.FactorsThrough presentVocabulary fineOrderEndpoint → ⊥
presentVocabularyCannotRecoverReceptionOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      interpretThenInstitutionalise
      institutionaliseThenInterpret
      refl
      orderEndpointsDiffer)

memoryStatus : ReceptionOrder → Collective.MemoryStatus
memoryStatus _ = Collective.transmittedMemory

institutionalLegibility : ReceptionOrder → Collective.PublicLegibility
institutionalLegibility _ = Collective.institutionallyLegible

sameTransmittedMemoryAcrossOrders :
  memoryStatus interpretThenInstitutionalise
  ≡ memoryStatus institutionaliseThenInterpret
sameTransmittedMemoryAcrossOrders = refl

sameInstitutionalLegibilityAcrossOrders :
  institutionalLegibility interpretThenInstitutionalise
  ≡ institutionalLegibility institutionaliseThenInterpret
sameInstitutionalLegibilityAcrossOrders = refl

------------------------------------------------------------------------
-- 5. Direct reuse of merged collective-memory and holonomy boundaries.
------------------------------------------------------------------------

transmittedMemoryStillDoesNotImplyInstitutionalContinuity :
  Collective.TransmittedMemoryImpliesInstitutionalContinuity → ⊥
transmittedMemoryStillDoesNotImplyInstitutionalContinuity =
  Collective.transmittedMemoryDoesNotImplyInstitutionalContinuity

publicLegibilityStillDoesNotDetermineInstitutionalOutcome :
  INF.FactorsThrough
    Collective.publicLegibilitySurface
    Collective.institutionalOutcome → ⊥
publicLegibilityStillDoesNotDetermineInstitutionalOutcome =
  Collective.publicLegibilityCannotRecoverInstitutionalOutcome

holonomyPrecedentKeepsGaugePromotionFalse :
  Holonomy.CubieHolonomyBoundary.literalGaugeConnectionConstructed
    Holonomy.canonicalCubieHolonomyBoundary
  ≡ false
holonomyPrecedentKeepsGaugePromotionFalse = refl

holonomyPrecedentKeepsWilsonLoopFalse :
  Holonomy.CubieHolonomyBoundary.wilsonLoopComputed
    Holonomy.canonicalCubieHolonomyBoundary
  ≡ false
holonomyPrecedentKeepsWilsonLoopFalse = refl

------------------------------------------------------------------------
-- 6. Source-attribution consequences.
------------------------------------------------------------------------

data LaterVocabularyPromotesOriginalMeaning : Set where
data TransmittedMemoryPromotesUnbrokenDoctrine : Set where
data InstitutionalisationPromotesSourceEndorsement : Set where
data ReceptionOrderDefectPromotesDialecticalNecessity : Set where
data ReceptionSquarePromotesGaugeCurvature : Set where
data SameReceptionStratumPromotesSameGenealogy : Set where
data CurrentUsePromotesUniqueReceptionHistory : Set where

laterVocabularyDoesNotPromoteOriginalMeaning :
  LaterVocabularyPromotesOriginalMeaning → ⊥
laterVocabularyDoesNotPromoteOriginalMeaning ()

transmittedMemoryDoesNotPromoteUnbrokenDoctrine :
  TransmittedMemoryPromotesUnbrokenDoctrine → ⊥
transmittedMemoryDoesNotPromoteUnbrokenDoctrine ()

institutionalisationDoesNotPromoteSourceEndorsement :
  InstitutionalisationPromotesSourceEndorsement → ⊥
institutionalisationDoesNotPromoteSourceEndorsement ()

receptionOrderDefectDoesNotPromoteDialecticalNecessity :
  ReceptionOrderDefectPromotesDialecticalNecessity → ⊥
receptionOrderDefectDoesNotPromoteDialecticalNecessity ()

receptionSquareDoesNotPromoteGaugeCurvature :
  ReceptionSquarePromotesGaugeCurvature → ⊥
receptionSquareDoesNotPromoteGaugeCurvature ()

sameReceptionStratumDoesNotPromoteSameGenealogy :
  SameReceptionStratumPromotesSameGenealogy → ⊥
sameReceptionStratumDoesNotPromoteSameGenealogy ()

currentUseDoesNotPromoteUniqueReceptionHistory :
  CurrentUsePromotesUniqueReceptionHistory → ⊥
currentUseDoesNotPromoteUniqueReceptionHistory ()

------------------------------------------------------------------------
-- 7. Canonical cross-pollination weld.
------------------------------------------------------------------------

record IntellectualReceptionStratifiedFibreWeld : Set where
  constructor intellectual-reception-stratified-fibre-weld
  field
    philosophyBoundary : Philosophy.PhilosophyClaimProvenanceHistoryBoundary
    wittgensteinBoundary : Wittgenstein.WittgensteinUsePracticeBoundary
    collectiveBoundary : Collective.SexedHistoricalCollectiveThresholdBoundary
    holonomyBoundary : Holonomy.CubieHolonomyBoundary
    coarseStratumOrderNonfactorability :
      INF.FactorsThrough coarseOrderSurface fineOrderEndpoint → ⊥
    presentVocabularyOrderNonfactorability :
      INF.FactorsThrough presentVocabulary fineOrderEndpoint → ⊥
    base369PR666Imported : Bool
    finiteReceptionSquareIsDASHIConstruction : Bool
    sourceAttributionSurvivesCrossPollination : Bool

canonicalIntellectualReceptionStratifiedFibreWeld :
  IntellectualReceptionStratifiedFibreWeld
canonicalIntellectualReceptionStratifiedFibreWeld =
  intellectual-reception-stratified-fibre-weld
    Philosophy.canonicalPhilosophyClaimProvenanceHistoryBoundary
    Wittgenstein.canonicalWittgensteinUsePracticeBoundary
    Collective.canonicalSexedHistoricalCollectiveThresholdBoundary
    Holonomy.canonicalCubieHolonomyBoundary
    coarseReceptionStratumCannotRecoverTransportOrder
    presentVocabularyCannotRecoverReceptionOrder
    false true true

------------------------------------------------------------------------
-- 8. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionStratifiedFibreBoundary : Set where
  constructor intellectual-reception-stratified-fibre-boundary
  field
    sameCoarseReceptionStratumDeterminesTransportOrder : Bool
    samePresentVocabularyDeterminesReceptionHistory : Bool
    transmittedMemoryDeterminesInstitutionalContinuity : Bool
    institutionalLegibilityDeterminesInstitutionalOutcome : Bool
    institutionalisationMeansSourceEndorsement : Bool
    laterVocabularyRecoversOriginalMeaning : Bool
    orderDefectIsGaugeCurvature : Bool
    orderDefectIsNecessaryDialectic : Bool
    receptionHistoryIsFibrewiseAndOrderSensitive : Bool
    sourceAttributionRemainsHistoryQualified : Bool

canonicalIntellectualReceptionStratifiedFibreBoundary :
  IntellectualReceptionStratifiedFibreBoundary
canonicalIntellectualReceptionStratifiedFibreBoundary =
  intellectual-reception-stratified-fibre-boundary
    false false false false false false false false true true
