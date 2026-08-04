module DASHI.Foundations.JPlusOneScaleBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import JFixedPoint as Fixed
import Moonshine as Moon
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage12
import DASHI.Foundations.StageValuationBundleAtlas as LegacyBundle

------------------------------------------------------------------------
-- Source calibration: J. H. Conway and S. P. Norton, "Monstrous
-- Moonshine", DOI 10.1112/blms/11.3.308; Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- DOI 10.1007/BF01232032.
--
-- Exact +1 and place-value facts already present in the repository.
--
-- The shared algebraic shape "carrier plus fresh unit" is formalised, while
-- local j-basis notation, decimal place value, Monster representation
-- dimension, the modular j-function and observation semantics remain distinct
-- typed surfaces.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The user's j-basis notation: j = 1, 10j = 10, 11j = 10j + j.
------------------------------------------------------------------------

jBasisUnit : Nat
jBasisUnit = 1

tenJ : Nat
tenJ = 10 * jBasisUnit

elevenJ : Nat
elevenJ = 11 * jBasisUnit

twelveJ : Nat
twelveJ = 12 * jBasisUnit

tenJIsTen : tenJ ≡ 10
tenJIsTen = refl

elevenJIsTenJPlusJ : tenJ + jBasisUnit ≡ elevenJ
elevenJIsTenJPlusJ = refl

twelveJIsTenJPlusTwoJ : tenJ + 2 * jBasisUnit ≡ twelveJ
twelveJIsTenJPlusTwoJ = refl

record FreshUnitExtension : Set where
  field
    carrierValue : Nat
    freshValue : Nat
    joinedValue : Nat
    joinExact : carrierValue + freshValue ≡ joinedValue
    interpretation : String

stage11FreshUnitExtension : FreshUnitExtension
stage11FreshUnitExtension = record
  { carrierValue = 10
  ; freshValue = 1
  ; joinedValue = 11
  ; joinExact = refl
  ; interpretation = "ten local j-units plus one fresh local j-unit"
  }

stage12FreshRelationExtension : FreshUnitExtension
stage12FreshRelationExtension = record
  { carrierValue = 10
  ; freshValue = 2
  ; joinedValue = 12
  ; joinExact = refl
  ; interpretation = "ten local j-units plus a two-j relation coordinate"
  }

moonshineFreshUnitExtension : FreshUnitExtension
moonshineFreshUnitExtension = record
  { carrierValue = Moon.rep-dim
  ; freshValue = 1
  ; joinedValue = Moon.j-coefficient
  ; joinExact = Moon.mckay
  ; interpretation = "McKay arithmetic: 196883 plus one equals the first nonconstant j coefficient 196884"
  }

legacyStage11JoinRecovered :
  LegacyBundle.Stage11CrossScaleJoin.carriedBundleValue
    LegacyBundle.canonicalStage11CrossScaleJoin
  +
  LegacyBundle.Stage11CrossScaleJoin.freshLocalValue
    LegacyBundle.canonicalStage11CrossScaleJoin
  ≡
  LegacyBundle.Stage11CrossScaleJoin.joinedValue
    LegacyBundle.canonicalStage11CrossScaleJoin
legacyStage11JoinRecovered =
  LegacyBundle.Stage11CrossScaleJoin.joinIsEleven
    LegacyBundle.canonicalStage11CrossScaleJoin

stage11JPlusOne :
  Stage12.decimalCarryUnit + Stage12.localJUnit ≡ Stage12.toNat Stage12.stage-11
stage11JPlusOne = refl

stage12JPlusTwo :
  Stage12.decimalCarryUnit + 2 * Stage12.localJUnit ≡ Stage12.toNat Stage12.stage-12
stage12JPlusTwo = refl

------------------------------------------------------------------------
-- Exact reuse of the existing unbounded DecimalStageAddress carrier.
------------------------------------------------------------------------

toLegacyDecimalAddress :
  Stage12.JScaleAddress →
  LegacyBundle.DecimalStageAddress
toLegacyDecimalAddress address = record
  { coarseBundles = Stage12.JScaleAddress.coarseJUnits address
  ; localOffset = Stage12.JScaleAddress.localOffset address
  ; globalIndex = Stage12.JScaleAddress.globalIndex address
  ; decomposition = Stage12.JScaleAddress.decomposition address
  }

stage12LegacyDecimalGlobalIndex :
  LegacyBundle.DecimalStageAddress.globalIndex
    (toLegacyDecimalAddress (Stage12.jAddress Stage12.stage-12))
  ≡ 12
stage12LegacyDecimalGlobalIndex = refl

moonshineCoefficientIsRepresentationPlusOne :
  Moon.rep-dim + 1 ≡ Moon.j-coefficient
moonshineCoefficientIsRepresentationPlusOne = Moon.mckay

unitObservationContractsTo196884 :
  Fixed.contract Fixed.unit-obs ≡ 196884
unitObservationContractsTo196884 = Fixed.unit-converges

record JPlusOneShapeAnalogy : Set where
  field
    stagePattern : FreshUnitExtension
    moonshinePattern : FreshUnitExtension
    commonCarrierPlusFreshUnitShape : Bool
    valuesIdentified : Bool
    semanticsIdentified : Bool
    bridgeReceipt : String

canonicalJPlusOneShapeAnalogy : JPlusOneShapeAnalogy
canonicalJPlusOneShapeAnalogy = record
  { stagePattern = stage11FreshUnitExtension
  ; moonshinePattern = moonshineFreshUnitExtension
  ; commonCarrierPlusFreshUnitShape = true
  ; valuesIdentified = false
  ; semanticsIdentified = false
  ; bridgeReceipt =
      "The exact equations 10+1=11 and 196883+1=196884 share an extension shape only; no equality of carriers or meanings is asserted."
  }

record JPlusOneAuthorityBoundary : Set where
  field
    exactStageArithmeticAvailable : Bool
    exactMcKayArithmeticAvailable : Bool
    unitObservationArithmeticAvailable : Bool
    existingDecimalAddressCarrierReused : Bool
    modularJEqualsLocalJUnitClaimed : Bool
    observerCreatesModularInvariantClaimed : Bool
    constantStackProvesAnalyticAttractorClaimed : Bool
    representationDimensionEqualsStageTenClaimed : Bool
    sharedShapeMaySeedCandidateInterpretation : Bool
    boundaryNote : String

canonicalJPlusOneAuthorityBoundary : JPlusOneAuthorityBoundary
canonicalJPlusOneAuthorityBoundary = record
  { exactStageArithmeticAvailable = true
  ; exactMcKayArithmeticAvailable = true
  ; unitObservationArithmeticAvailable = true
  ; existingDecimalAddressCarrierReused = true
  ; modularJEqualsLocalJUnitClaimed = false
  ; observerCreatesModularInvariantClaimed = false
  ; constantStackProvesAnalyticAttractorClaimed = false
  ; representationDimensionEqualsStageTenClaimed = false
  ; sharedShapeMaySeedCandidateInterpretation = true
  ; boundaryNote =
      "The bridge reuses the existing DecimalStageAddress and imports exact arithmetic from Moonshine and JFixedPoint, but does not promote legacy observer, heat, convergence or ontology commentary."
  }
