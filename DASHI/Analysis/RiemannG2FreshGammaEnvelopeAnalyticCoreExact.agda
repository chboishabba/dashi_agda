module DASHI.Analysis.RiemannG2FreshGammaEnvelopeAnalyticCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as SameTaper

------------------------------------------------------------------------
-- LEAST-PRIVILEGE FRESH GAMMA ANALYTIC CORE
--
-- GammaAnalyticCore contains only theorem-bearing Gamma analysis.  Literal
-- equality with the final consumer taper is a separate representation
-- attachment and therefore is not a primitive hypothesis of this producer.
------------------------------------------------------------------------

record FreshGammaEnvelopeCoreInput : Set₁ where
  field
    Scalar : Set
    Taper : Set
    _≤_ : Scalar -> Scalar -> Set

    gammaResponse : Taper -> Scalar
    gammaEnvelope : Taper -> Scalar
    universalPoleQuotientTaper : Taper

    gammaResponseBelowEnvelope :
      _≤_
        (gammaResponse universalPoleQuotientTaper)
        (gammaEnvelope universalPoleQuotientTaper)

    assignedGammaAllowance : Scalar

    envelopeBelowAssignedAllowance :
      _≤_
        (gammaEnvelope universalPoleQuotientTaper)
        assignedGammaAllowance

    analyticReference : String

open FreshGammaEnvelopeCoreInput public

compileGammaTarget :
  FreshGammaEnvelopeCoreInput ->
  Gamma.PoleQuotientGammaBudgetTarget
compileGammaTarget input =
  Gamma.pole-quotient-gamma-budget-target
    (Scalar input)
    (Taper input)
    (gammaResponse input)
    (gammaEnvelope input)
    (_≤_ input)
    (universalPoleQuotientTaper input)
    (gammaResponseBelowEnvelope input)

compileGammaAnalyticCore :
  FreshGammaEnvelopeCoreInput ->
  Core.GammaAnalyticCore
compileGammaAnalyticCore input =
  Core.gamma-analytic-core
    (compileGammaTarget input)
    (assignedGammaAllowance input)
    (envelopeBelowAssignedAllowance input)
    (analyticReference input)

------------------------------------------------------------------------
-- THE EXISTING SAME-TAPER PAYMENT ROUTE IS A STRONGER SUFFICIENT PRODUCER
------------------------------------------------------------------------

fromSameTaperRoute :
  (envelope : SameTaper.FreshSameTaperGammaEnvelope) ->
  SameTaper.FreshSameTaperGammaAllowanceInput envelope ->
  FreshGammaEnvelopeCoreInput
fromSameTaperRoute envelope allowance = record
  { Scalar = SameTaper.Scalar envelope
  ; Taper = SameTaper.Taper envelope
  ; _≤_ = SameTaper._≤_ envelope
  ; gammaResponse = SameTaper.gammaResponse envelope
  ; gammaEnvelope = SameTaper.gammaEnvelope envelope
  ; universalPoleQuotientTaper =
      SameTaper.universalPoleQuotientTaper envelope
  ; gammaResponseBelowEnvelope =
      SameTaper.gammaResponseBelowEnvelope envelope
  ; assignedGammaAllowance =
      SameTaper.assignedGammaAllowance allowance
  ; envelopeBelowAssignedAllowance =
      SameTaper.gammaEnvelopeBelowAssignedAllowance allowance
  ; analyticReference = SameTaper.producerReference envelope
  }

sameTaperRouteCompilesGammaAnalyticCore :
  (envelope : SameTaper.FreshSameTaperGammaEnvelope) ->
  (allowance : SameTaper.FreshSameTaperGammaAllowanceInput envelope) ->
  Core.GammaAnalyticCore
sameTaperRouteCompilesGammaAnalyticCore envelope allowance =
  compileGammaAnalyticCore (fromSameTaperRoute envelope allowance)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record FreshGammaEnvelopeCoreBoundary : Set where
  constructor fresh-gamma-envelope-core-boundary
  field
    historical8889IdentityRequired : Bool
    historical8889IdentityRequiredIsFalse :
      historical8889IdentityRequired ≡ false

    sameFinalTaperReceiptRequiredToConstructGammaCore : Bool
    sameFinalTaperReceiptRequiredToConstructGammaCoreIsFalse :
      sameFinalTaperReceiptRequiredToConstructGammaCore ≡ false

    responseBelowFreshEnvelopeRequired : Bool
    responseBelowFreshEnvelopeRequiredIsTrue :
      responseBelowFreshEnvelopeRequired ≡ true

    envelopeBelowAssignedAllowanceRequired : Bool
    envelopeBelowAssignedAllowanceRequiredIsTrue :
      envelopeBelowAssignedAllowanceRequired ≡ true

    sameFinalTaperReceiptRemainsDownstreamRepresentationWork : Bool
    sameFinalTaperReceiptRemainsDownstreamRepresentationWorkIsTrue :
      sameFinalTaperReceiptRemainsDownstreamRepresentationWork ≡ true

    historicalSameTaperRouteStillSufficient : Bool
    historicalSameTaperRouteStillSufficientIsTrue :
      historicalSameTaperRouteStillSufficient ≡ true

    gammaAnalyticCoreCompiles : Bool
    gammaAnalyticCoreCompilesIsTrue : gammaAnalyticCoreCompiles ≡ true

    gammaAnalyticCoreInhabitedHere : Bool
    gammaAnalyticCoreInhabitedHereIsFalse :
      gammaAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFreshGammaEnvelopeCoreBoundary : FreshGammaEnvelopeCoreBoundary
canonicalFreshGammaEnvelopeCoreBoundary =
  fresh-gamma-envelope-core-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "For GammaAnalyticCore itself, prove GammaResponse(g)<=GammaEnvelope(g) on one chosen universal taper and GammaEnvelope(g)<=A_Gamma. Historical 8889 producer identity and literal equality with the final consumer taper are not analytic-core hypotheses. The final-taper identity remains mandatory later as GammaRepresentationAttachment. The existing FreshSameTaperGammaEnvelope route projects to this smaller core input, so it remains sufficient rather than mandatory. No Gamma core inhabitant or RH theorem is fabricated here."
