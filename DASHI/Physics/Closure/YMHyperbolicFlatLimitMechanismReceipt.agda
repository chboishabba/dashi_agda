module DASHI.Physics.Closure.YMHyperbolicFlatLimitMechanismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills hyperbolic flat-limit mechanism receipt.
--
-- This receipt records a candidate mechanism for making the hyperbolic
-- Shimura/Drinfeld carrier geometry look flat in a limiting regime.  The
-- mechanism is deliberately candidate-only: Drinfeld modular curves and
-- function-field analogues supply a non-archimedean route, the q -> infinity
-- or p-adic Shimura limit supplies the flat-limit heuristic, and p-adic YM on
-- a Bruhat-Tits tree is cited as authority for tree-like YM structure.
-- No Euclidean universality theorem, continuum YM proof, Clay promotion, or
-- terminal claim is introduced here.

data YMFlatLimitCandidateStatus : Set where
  candidate :
    YMFlatLimitCandidateStatus

data YMHyperbolicFlatLimitMechanismStatus : Set where
  hyperbolicFlatLimitMechanismCandidateRecorded :
    YMHyperbolicFlatLimitMechanismStatus

data YMFlatLimitGeometryFeature : Set where
  drinfeldModularCurves :
    YMFlatLimitGeometryFeature

  functionFieldAnalogue :
    YMFlatLimitGeometryFeature

  qToInfinityLimit :
    YMFlatLimitGeometryFeature

  nonArchimedeanShimuraLimit :
    YMFlatLimitGeometryFeature

  pAdicShimuraLimit :
    YMFlatLimitGeometryFeature

  bruhatTitsTreePGL2FqLaurentSeries :
    YMFlatLimitGeometryFeature

  pAdicTreeLikeGeometry :
    YMFlatLimitGeometryFeature

canonicalYMFlatLimitGeometryFeatures :
  List YMFlatLimitGeometryFeature
canonicalYMFlatLimitGeometryFeatures =
  drinfeldModularCurves
  ∷ functionFieldAnalogue
  ∷ qToInfinityLimit
  ∷ nonArchimedeanShimuraLimit
  ∷ pAdicShimuraLimit
  ∷ bruhatTitsTreePGL2FqLaurentSeries
  ∷ pAdicTreeLikeGeometry
  ∷ []

data YMFlatLimitAuthorityCitation : Set where
  Gubser2017 :
    YMFlatLimitAuthorityCitation

data YMFlatLimitCitationAuthority : Set where
  citationAuthority :
    YMFlatLimitAuthorityCitation →
    YMFlatLimitCitationAuthority

pAdicYMOnTree :
  YMFlatLimitCitationAuthority
pAdicYMOnTree =
  citationAuthority Gubser2017

data YMFlatLimitMechanism : Set where
  pAdicShimuraCurve :
    YMFlatLimitCandidateStatus →
    YMFlatLimitMechanism

flatLimitFromDrinfeldOrPAdicShimura :
  YMFlatLimitCandidateStatus
flatLimitFromDrinfeldOrPAdicShimura =
  candidate

pAdicTreeApproximatesEuclideanSpace :
  YMFlatLimitCandidateStatus
pAdicTreeApproximatesEuclideanSpace =
  candidate

ymFlatLimitMechanism :
  YMFlatLimitMechanism
ymFlatLimitMechanism =
  pAdicShimuraCurve candidate

data YMFlatLimitOpenObligation : Set where
  proveTreeLimitEuclideanUniversality :
    YMFlatLimitOpenObligation

  proveQToInfinityFlatContinuumLimit :
    YMFlatLimitOpenObligation

  transferPAdicTreeYMToFourDimensionalEuclideanYM :
    YMFlatLimitOpenObligation

  proveClayMassGapSurvival :
    YMFlatLimitOpenObligation

canonicalYMFlatLimitOpenObligations :
  List YMFlatLimitOpenObligation
canonicalYMFlatLimitOpenObligations =
  proveTreeLimitEuclideanUniversality
  ∷ proveQToInfinityFlatContinuumLimit
  ∷ transferPAdicTreeYMToFourDimensionalEuclideanYM
  ∷ proveClayMassGapSurvival
  ∷ []

data YMHyperbolicFlatLimitPromotion : Set where

ymHyperbolicFlatLimitPromotionImpossibleHere :
  YMHyperbolicFlatLimitPromotion →
  ⊥
ymHyperbolicFlatLimitPromotionImpossibleHere ()

drinfeldPAdicShimuraFlatLimitStatement : String
drinfeldPAdicShimuraFlatLimitStatement =
  "Candidate flat-limit mechanism: replace the hyperbolic Shimura carrier by a Drinfeld/function-field or p-adic Shimura limit; as q -> infinity or in a non-archimedean p-adic limit, the Bruhat-Tits tree of PGL2(F_q((t))) supplies tree-like geometry, with p-adic YM on trees cited via Gubser2017.  This is candidate evidence only, not a Euclidean universality theorem or Clay promotion."

record YMHyperbolicFlatLimitMechanismReceipt : Setω where
  field
    status :
      YMHyperbolicFlatLimitMechanismStatus

    flatLimitFromDrinfeldOrPAdicShimuraField :
      YMFlatLimitCandidateStatus

    flatLimitFromDrinfeldOrPAdicShimuraIsCandidate :
      flatLimitFromDrinfeldOrPAdicShimuraField
      ≡
      flatLimitFromDrinfeldOrPAdicShimura

    pAdicYMOnTreeAuthority :
      YMFlatLimitCitationAuthority

    pAdicYMOnTreeAuthorityIsCanonical :
      pAdicYMOnTreeAuthority ≡ pAdicYMOnTree

    pAdicTreeApproximatesEuclideanSpaceField :
      YMFlatLimitCandidateStatus

    pAdicTreeApproximatesEuclideanSpaceIsCandidate :
      pAdicTreeApproximatesEuclideanSpaceField
      ≡
      pAdicTreeApproximatesEuclideanSpace

    ymFlatLimitMechanismField :
      YMFlatLimitMechanism

    ymFlatLimitMechanismIsCanonical :
      ymFlatLimitMechanismField ≡ ymFlatLimitMechanism

    geometryFeatures :
      List YMFlatLimitGeometryFeature

    geometryFeaturesAreCanonical :
      geometryFeatures ≡ canonicalYMFlatLimitGeometryFeatures

    drinfeldModularCurveRouteRecorded :
      Bool

    drinfeldModularCurveRouteRecordedIsTrue :
      drinfeldModularCurveRouteRecorded ≡ true

    functionFieldAnalogueRouteRecorded :
      Bool

    functionFieldAnalogueRouteRecordedIsTrue :
      functionFieldAnalogueRouteRecorded ≡ true

    qToInfinityFlatLimitRecorded :
      Bool

    qToInfinityFlatLimitRecordedIsTrue :
      qToInfinityFlatLimitRecorded ≡ true

    nonArchimedeanOrPAdicShimuraLimitRecorded :
      Bool

    nonArchimedeanOrPAdicShimuraLimitRecordedIsTrue :
      nonArchimedeanOrPAdicShimuraLimitRecorded ≡ true

    bruhatTitsTreePGL2FqLaurentSeriesRecorded :
      Bool

    bruhatTitsTreePGL2FqLaurentSeriesRecordedIsTrue :
      bruhatTitsTreePGL2FqLaurentSeriesRecorded ≡ true

    pAdicTreeGeometryRecorded :
      Bool

    pAdicTreeGeometryRecordedIsTrue :
      pAdicTreeGeometryRecorded ≡ true

    euclideanUniversalityConstructed :
      Bool

    euclideanUniversalityConstructedIsFalse :
      euclideanUniversalityConstructed ≡ false

    continuumYMConstructed :
      Bool

    continuumYMConstructedIsFalse :
      continuumYMConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    openObligations :
      List YMFlatLimitOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMFlatLimitOpenObligations

    statement :
      String

    statementIsCanonical :
      statement ≡ drinfeldPAdicShimuraFlatLimitStatement

    promotionFlags :
      List YMHyperbolicFlatLimitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMHyperbolicFlatLimitMechanismReceipt public

canonicalYMHyperbolicFlatLimitMechanismReceipt :
  YMHyperbolicFlatLimitMechanismReceipt
canonicalYMHyperbolicFlatLimitMechanismReceipt =
  record
    { status =
        hyperbolicFlatLimitMechanismCandidateRecorded
    ; flatLimitFromDrinfeldOrPAdicShimuraField =
        candidate
    ; flatLimitFromDrinfeldOrPAdicShimuraIsCandidate =
        refl
    ; pAdicYMOnTreeAuthority =
        citationAuthority Gubser2017
    ; pAdicYMOnTreeAuthorityIsCanonical =
        refl
    ; pAdicTreeApproximatesEuclideanSpaceField =
        candidate
    ; pAdicTreeApproximatesEuclideanSpaceIsCandidate =
        refl
    ; ymFlatLimitMechanismField =
        pAdicShimuraCurve candidate
    ; ymFlatLimitMechanismIsCanonical =
        refl
    ; geometryFeatures =
        canonicalYMFlatLimitGeometryFeatures
    ; geometryFeaturesAreCanonical =
        refl
    ; drinfeldModularCurveRouteRecorded =
        true
    ; drinfeldModularCurveRouteRecordedIsTrue =
        refl
    ; functionFieldAnalogueRouteRecorded =
        true
    ; functionFieldAnalogueRouteRecordedIsTrue =
        refl
    ; qToInfinityFlatLimitRecorded =
        true
    ; qToInfinityFlatLimitRecordedIsTrue =
        refl
    ; nonArchimedeanOrPAdicShimuraLimitRecorded =
        true
    ; nonArchimedeanOrPAdicShimuraLimitRecordedIsTrue =
        refl
    ; bruhatTitsTreePGL2FqLaurentSeriesRecorded =
        true
    ; bruhatTitsTreePGL2FqLaurentSeriesRecordedIsTrue =
        refl
    ; pAdicTreeGeometryRecorded =
        true
    ; pAdicTreeGeometryRecordedIsTrue =
        refl
    ; euclideanUniversalityConstructed =
        false
    ; euclideanUniversalityConstructedIsFalse =
        refl
    ; continuumYMConstructed =
        false
    ; continuumYMConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; openObligations =
        canonicalYMFlatLimitOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; statement =
        drinfeldPAdicShimuraFlatLimitStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Flat-limit route is candidate-only through Drinfeld modular curves/function-field analogues"
        ∷ "The limiting heuristic is q -> infinity or a non-archimedean/p-adic Shimura limit"
        ∷ "Bruhat-Tits tree geometry for PGL2(F_q((t))) is recorded as the tree-like carrier"
        ∷ "p-adic YM on a tree is citation-authorized by Gubser2017"
        ∷ "p-adic tree approximation to Euclidean space remains candidate-valued"
        ∷ "No Euclidean universality, continuum YM, Clay, or terminal promotion is made here"
        ∷ []
    }

ymHyperbolicFlatLimitKeepsClayFalse :
  clayYangMillsPromoted canonicalYMHyperbolicFlatLimitMechanismReceipt
  ≡
  false
ymHyperbolicFlatLimitKeepsClayFalse =
  refl

ymHyperbolicFlatLimitKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYMHyperbolicFlatLimitMechanismReceipt
  ≡
  false
ymHyperbolicFlatLimitKeepsTerminalFalse =
  refl

ymHyperbolicFlatLimitNoPromotion :
  YMHyperbolicFlatLimitPromotion →
  ⊥
ymHyperbolicFlatLimitNoPromotion =
  ymHyperbolicFlatLimitPromotionImpossibleHere
