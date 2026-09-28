module DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact where

------------------------------------------------------------------------
-- pB INTEGRAL / MOD-p TATE-COHOMOLOGY MOONSHINE BRIDGE
--
-- EXTERNAL SOURCE
--
-- Scott Carnahan, "A Self-Dual Integral Form of the Moonshine Module",
-- Corollary 3.25 ("newer modular moonshine"):
--
-- There exists a Monster-stable self-dual integral form V_Z of V^natural such
-- that, for every prime-order Monster element g, graded Brauer characters of
-- p-regular h in C_M(g) on Tate cohomology H^*(g,V_Z) are explicit
-- McKay--Thompson combinations.
--
-- In particular:
--
--   g = 2B:
--     Tr(h | H^0) = ( T_gh(tau) + T_gh(tau+1/2) ) / 2
--     Tr(h | H^1) = ( T_gh(tau) - T_gh(tau+1/2) ) / 2
--
--   g = pB, 2 | (p-1), hence in particular g = 3B:
--     Tr(h | H^0) = ( T_gh(tau) + T_ghsigma(tau) ) / 2
--     Tr(h | H^1) = ( T_gh(tau) - T_ghsigma(tau) ) / 2,
--
-- where sigma is the distinguished involution in the relevant centralizer
-- quotient described in the source.
--
-- CONSEQUENCE
--
-- The pB integral/mod-p centralizer object is SOURCE-BACKED.  The remaining
-- theorem is not its existence.  It is the recognition/localization map from
-- this Tate-cohomology object to the p=N Igusa/wild bad-level term whose
-- source-native valuation is 10 at p=2 and 2 at p=3.
--
-- ATTRIBUTION
--
-- Carnahan owns the integral form and modular-moonshine Tate character
-- formulas.  DASHI owns the typed application to the 2B/3B bad-level cutset.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

carnahanIntegralForm : Source.AttributedSource
carnahanIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "SIGMA 15 (2019), 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 proves the stronger modular moonshine conjecture unconditionally from a Monster-stable self-dual integral form; includes explicit Tate-cohomology Brauer-character formulas for 2B and pB classes such as 3B. Does not identify the DASHI bad-level Igusa valuation 10/2"
    Source.publicAttribution

pbIntegralTateSourceAtlas : Source.AttributedSourceAtlas
pbIntegralTateSourceAtlas =
  Source.mkSourceAtlas
    "pB integral Tate-cohomology modular-moonshine bridge"
    "DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact"
    (carnahanIntegralForm ∷ [])
    "Carnahan owns the self-dual integral form and pB Tate-cohomology McKay--Thompson formulas; DASHI owns only the later bad-level recognition/valuation obligation"

------------------------------------------------------------------------
-- 2. Typed pB lanes and source-backed formulas.
------------------------------------------------------------------------

data PBPrimeLane : Set where
  lane2B lane3B : PBPrimeLane

data TateParity : Set where
  tateH0 tateH1 : TateParity

data PBTraceTransform : Set where
  twoBHalfTranslation :
    PBTraceTransform

  oddPBInvolutionCompanion :
    PBTraceTransform

traceTransform :
  PBPrimeLane ->
  PBTraceTransform
traceTransform lane2B =
  twoBHalfTranslation
traceTransform lane3B =
  oddPBInvolutionCompanion

data TraceCombination : Set where
  halfSum :
    TraceCombination
  halfDifference :
    TraceCombination

tateTraceCombination :
  TateParity ->
  TraceCombination
tateTraceCombination tateH0 = halfSum
tateTraceCombination tateH1 = halfDifference

------------------------------------------------------------------------
-- 3. Source receipt: what is paid by Corollary 3.25.
------------------------------------------------------------------------

record PBIntegralTateCohomologyReceipt : Set where
  constructor pb-integral-tate-cohomology-receipt
  field
    monsterStableSelfDualIntegralFormExists :
      Bool

    primeOrderTateCohomologyCarriesCentralizerBrauerCharacters :
      Bool

    twoBFormulaUsesHalfTranslation :
      Bool

    oddPBFormulaUsesDistinguishedCentralizerInvolution :
      Bool

    threeBIncludedInOddPBCase :
      Bool

    formulasAreUnconditionalAfterIntegralFormConstruction :
      Bool

    givesIntegralOrModPBridgeRatherThanOnlyComplexTwistedSector :
      Bool

canonicalPBIntegralTateCohomologyReceipt :
  PBIntegralTateCohomologyReceipt
canonicalPBIntegralTateCohomologyReceipt =
  pb-integral-tate-cohomology-receipt
    true true true true true true true

------------------------------------------------------------------------
-- 4. What remains distinct from the bad-level analytic fourth term.
------------------------------------------------------------------------

data PBIntegralTateObject : Set where
  twoBTateObject :
    PBIntegralTateObject
  threeBTateObject :
    PBIntegralTateObject

pbObject :
  PBPrimeLane ->
  PBIntegralTateObject
pbObject lane2B = twoBTateObject
pbObject lane3B = threeBTateObject

localDefect :
  PBPrimeLane ->
  Nat
localDefect lane2B =
  Local.p2LocalCentralizerResidual
localDefect lane3B =
  Local.p3LocalCentralizerResidual

data TateCohomologyFormulaDefinesBadLevelValuation : Set where
data TateObjectIsIgusaLocalObjectByDefinition : Set where
data HalfSumDifferenceOrderEqualsMonsterResidual : Set where
data IntegralTateBridgeAutomaticallyCreatesPadicTwistedSector : Set where

tateFormulaDoesNotDefineBadLevelValuation :
  TateCohomologyFormulaDefinesBadLevelValuation -> ⊥
tateFormulaDoesNotDefineBadLevelValuation ()

tateObjectNotIdentifiedWithIgusaObjectByDefinition :
  TateObjectIsIgusaLocalObjectByDefinition -> ⊥
tateObjectNotIdentifiedWithIgusaObjectByDefinition ()

halfSumDifferenceDoesNotAutomaticallyHaveResidualOrder :
  HalfSumDifferenceOrderEqualsMonsterResidual -> ⊥
halfSumDifferenceDoesNotAutomaticallyHaveResidualOrder ()

integralTateBridgeDoesNotAutomaticallyCreatePadicTwistedSector :
  IntegralTateBridgeAutomaticallyCreatesPadicTwistedSector -> ⊥
integralTateBridgeDoesNotAutomaticallyCreatePadicTwistedSector ()

------------------------------------------------------------------------
-- 5. Sharpened comparison theorem target.
------------------------------------------------------------------------

record PBIntegralTateToBadLevelValuationAuthority : Set₁ where
  field
    BadLevelLocalizedTateObject : Set

    localizeIntegralTateObject :
      PBIntegralTateObject ->
      BadLevelLocalizedTateObject

    valuation :
      PBPrimeLane ->
      BadLevelLocalizedTateObject ->
      Nat

    localizationComesFromCarnahanTateObject :
      Bool
    localizationComesFromCarnahanTateObjectIsTrue :
      localizationComesFromCarnahanTateObject ≡ true

    localizationUsesPrimeEqualsLevelIgusaGeometry :
      Bool
    localizationUsesPrimeEqualsLevelIgusaGeometryIsTrue :
      localizationUsesPrimeEqualsLevelIgusaGeometry ≡ true

    preservesPBMonsterLocalCentralizerAction :
      Bool
    preservesPBMonsterLocalCentralizerActionIsTrue :
      preservesPBMonsterLocalCentralizerAction ≡ true

    twoBValuationIsTen :
      valuation lane2B (localizeIntegralTateObject twoBTateObject) ≡ 10

    threeBValuationIsTwo :
      valuation lane3B (localizeIntegralTateObject threeBTateObject) ≡ 2

    twoBValuationRecognisesIndependentDefect :
      valuation lane2B (localizeIntegralTateObject twoBTateObject)
      ≡ localDefect lane2B

    threeBValuationRecognisesIndependentDefect :
      valuation lane3B (localizeIntegralTateObject threeBTateObject)
      ≡ localDefect lane3B

    proofDoesNotReadTargetTenTwo :
      Bool
    proofDoesNotReadTargetTenTwoIsTrue :
      proofDoesNotReadTargetTenTwo ≡ true

open PBIntegralTateToBadLevelValuationAuthority public

data PBIntegralTateToBadLevelValuationAuthorityInhabited : Set where

pbIntegralTateToBadLevelValuationStillOpen :
  PBIntegralTateToBadLevelValuationAuthorityInhabited -> ⊥
pbIntegralTateToBadLevelValuationStillOpen ()

------------------------------------------------------------------------
-- 6. Attribution boundary.
------------------------------------------------------------------------

data CarnahanCreditedWithIgusaLocalization : Set where
data CarnahanCreditedWithTenTwoValuation : Set where

carnahanNotCreditedWithIgusaLocalization :
  CarnahanCreditedWithIgusaLocalization -> ⊥
carnahanNotCreditedWithIgusaLocalization ()

carnahanNotCreditedWithTenTwoValuation :
  CarnahanCreditedWithTenTwoValuation -> ⊥
carnahanNotCreditedWithTenTwoValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PBIntegralTateBridgeBoundary : Set where
  constructor pb-integral-tate-bridge-boundary
  field
    selfDualIntegralMonsterFormSourced : Bool
    twoBIntegralTateCentralizerFormulaSourced : Bool
    threeBIntegralTateCentralizerFormulaSourced : Bool
    pBIntegralModPObjectExistencePaid : Bool
    badLevelIgusaLocalizationPaid : Bool
    tenTwoValuationPaid : Bool
    localizationAuthoritySpecified : Bool
    localizationAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalPBIntegralTateBridgeBoundary :
  PBIntegralTateBridgeBoundary
canonicalPBIntegralTateBridgeBoundary =
  pb-integral-tate-bridge-boundary
    true true true true false false true false true
