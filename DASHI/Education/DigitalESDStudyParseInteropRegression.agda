module DASHI.Education.DigitalESDStudyParseInteropRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyParseInteropExact as Parse

genericParserIsReused :
  Parse.reusesGenericSLRParser Parse.canonicalStudyParseInteropBoundary ≡ true
genericParserIsReused = refl

nineteenCoordinatesRemainReviewGated :
  Parse.parserMayPayExtractionCoordinate Parse.canonicalStudyParseInteropBoundary ≡ false
nineteenCoordinatesRemainReviewGated = refl

resolutionLaneCannotBecomeAuditLane :
  Parse.ScreeningResolutionParseCreatesStudyAuditPacket → ⊥
resolutionLaneCannotBecomeAuditLane =
  Parse.screeningResolutionParseDoesNotCreateStudyAuditPacket

parserCannotCreateAdmission :
  Parse.ParserOutputCreatesSourceAuditAdmission → ⊥
parserCannotCreateAdmission =
  Parse.parserOutputDoesNotCreateSourceAuditAdmission

parserCannotRaiseClaimCeiling :
  Parse.ParserOutputRaisesStudyClaimCeiling → ⊥
parserCannotRaiseClaimCeiling =
  Parse.parserOutputDoesNotRaiseStudyClaimCeiling

unreportedDemographicsStayUnreported :
  Parse.ParserInfersAbsentGroupFromUnreportedDemographics → ⊥
unreportedDemographicsStayUnreported =
  Parse.parserDoesNotInferAbsentGroupFromUnreportedDemographics
