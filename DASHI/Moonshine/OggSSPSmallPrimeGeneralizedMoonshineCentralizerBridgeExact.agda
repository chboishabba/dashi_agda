module DASHI.Moonshine.OggSSPSmallPrimeGeneralizedMoonshineCentralizerBridgeExact where

------------------------------------------------------------------------
-- GENERALIZED-MOONSHINE CENTRALIZER -> MODULAR-FUNCTION BRIDGE
--
-- EXTERNAL SOURCE INPUT
--
-- Carnahan's generalized moonshine programme constructs, for each Monster
-- element g, twisted V^natural data carrying a projective action of C_M(g),
-- and proves the generalized moonshine modular-function/Hauptmodul statements.
--
-- His later orbifold-duality work handles non-Fricke Monster elements through
-- fixed-point-free Leech-lattice orbifolds and Conway-side data.
--
-- Dong--Li--Mason give earlier explicit twisted-sector existence results
-- including the 2B class.
--
-- CONSEQUENCE FOR THIS LANE
--
-- It is source-backed that Monster LOCAL CENTRALIZERS and modular functions
-- meet on a common twisted-module object.  This is substantially stronger than
-- merely observing that their p-adic orders match.
--
-- UNPAID STEP
--
-- No cited source computes the specific bad-level p,p^2 local q-expansion /
-- Hauptmodul valuation needed to identify the Duncan--Swisher exceptional
-- defects 10 and 2 with the 2B/3B local-centralizer defects.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

carnahanGMIV : Source.AttributedSource
carnahanGMIV =
  Source.mkNoDOISource
    "Scott Carnahan"
    "Generalized Moonshine IV: Monstrous Lie algebras"
    "arXiv:1208.6254 / generalized moonshine"
    "2012"
    "https://arxiv.org/abs/1208.6254"
    Source.academicArticleSource
    "for each Monster element, constructs twisted-module/Monstrous-Lie-algebra data with projective centralizer action and proves generalized-moonshine modular-function results; this source does not state the DASHI small-prime 10/2 valuation bridge"
    Source.publicAttribution

carnahan51 : Source.AttributedSource
carnahan51 =
  Source.mkNoDOISource
    "Scott Carnahan"
    "51 constructions of the Moonshine module"
    "arXiv:1707.02954"
    "2017"
    "https://arxiv.org/abs/1707.02954"
    Source.academicArticleSource
    "orbifold-duality source for non-Fricke Monster elements and fixed-point-free Leech-lattice automorphisms; supplies a centralizer/modular-orbifold framework, not the exceptional small-prime valuation theorem"
    Source.publicAttribution

dongLiMason : Source.AttributedSource
dongLiMason =
  Source.mkNoDOISource
    "Chongying Dong, Haisheng Li, and Geoffrey Mason"
    "Some twisted sectors for the Moonshine Module"
    "arXiv:q-alg/9504014"
    "1995"
    "https://arxiv.org/abs/q-alg/9504014"
    Source.academicArticleSource
    "explicit existence and uniqueness results for Monster twisted sectors including class 2B; modular graded-trace results are source precedent only and do not compute the DASHI bad-level fourth term"
    Source.publicAttribution

generalizedMoonshineCentralizerAtlas : Source.AttributedSourceAtlas
generalizedMoonshineCentralizerAtlas =
  Source.mkSourceAtlas
    "generalized moonshine centralizer/modular-function bridge"
    "DASHI.Moonshine.OggSSPSmallPrimeGeneralizedMoonshineCentralizerBridgeExact"
    (carnahanGMIV ∷ carnahan51 ∷ dongLiMason ∷ [])
    "external sources own twisted-module centralizer actions and generalized-moonshine modularity; DASHI owns the proposed recognition route from bad-level Igusa/inertia valuation to the 2B/3B local-centralizer defects"

------------------------------------------------------------------------
-- 1. Source-backed bridge shape.
------------------------------------------------------------------------

record GeneralizedMoonshineCentralizerModularBridge : Set₁ where
  field
    TwistedObject : Set

    p2TwistedObject :
      TwistedObject

    p3TwistedObject :
      TwistedObject

    centralizerActsProjectively :
      Bool
    centralizerActsProjectivelyIsTrue :
      centralizerActsProjectively ≡ true

    gradedTraceIsModularFunction :
      Bool
    gradedTraceIsModularFunctionIsTrue :
      gradedTraceIsModularFunction ≡ true

    p2CentralizerIsMonster2BLocal :
      Bool
    p2CentralizerIsMonster2BLocalIsTrue :
      p2CentralizerIsMonster2BLocal ≡ true

    p3CentralizerIsMonster3BLocal :
      Bool
    p3CentralizerIsMonster3BLocalIsTrue :
      p3CentralizerIsMonster3BLocal ≡ true

open GeneralizedMoonshineCentralizerModularBridge public

------------------------------------------------------------------------
-- 2. Analytic refinement needed for the Duncan--Swisher exceptional term.
------------------------------------------------------------------------

record SmallPrimeTwistedTraceValuationAuthority
    (bridge : GeneralizedMoonshineCentralizerModularBridge) : Set₁ where
  field
    BadLevelLocalTerm : Set

    p2BadLevelTerm :
      BadLevelLocalTerm

    p3BadLevelTerm :
      BadLevelLocalTerm

    valuation :
      BadLevelLocalTerm ->
      Nat

    p2ValuationIsLocalCentralizerDefect :
      valuation p2BadLevelTerm
      ≡ Local.p2LocalCentralizerResidual

    p3ValuationIsLocalCentralizerDefect :
      valuation p3BadLevelTerm
      ≡ Local.p3LocalCentralizerResidual

    badLevelTermComesFromTwistedTrace :
      Bool
    badLevelTermComesFromTwistedTraceIsTrue :
      badLevelTermComesFromTwistedTrace ≡ true

    compatibleWithLevelsPAndPSquared :
      Bool
    compatibleWithLevelsPAndPSquaredIsTrue :
      compatibleWithLevelsPAndPSquared ≡ true

    compatibleWithFrickeAtkinLehner :
      Bool
    compatibleWithFrickeAtkinLehnerIsTrue :
      compatibleWithFrickeAtkinLehner ≡ true

    proofIndependentOfTargetMonsterOrder :
      Bool
    proofIndependentOfTargetMonsterOrderIsTrue :
      proofIndependentOfTargetMonsterOrder ≡ true

open SmallPrimeTwistedTraceValuationAuthority public

------------------------------------------------------------------------
-- 3. Promotion firewalls.
------------------------------------------------------------------------

data GeneralizedMoonshineAloneProvesTenTwo : Set where
data CentralizerActionAloneProvesBadLevelValuation : Set where
data TwistedTraceValuationAuthorityInhabited : Set where

generalizedMoonshineAloneDoesNotProveTenTwo :
  GeneralizedMoonshineAloneProvesTenTwo -> ⊥
generalizedMoonshineAloneDoesNotProveTenTwo ()

centralizerActionDoesNotProveBadLevelValuation :
  CentralizerActionAloneProvesBadLevelValuation -> ⊥
centralizerActionDoesNotProveBadLevelValuation ()

twistedTraceValuationStillOpen :
  TwistedTraceValuationAuthorityInhabited -> ⊥
twistedTraceValuationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record GeneralizedMoonshineCentralizerBridgeBoundary : Set where
  constructor generalized-moonshine-centralizer-bridge-boundary
  field
    monsterCentralizerActsOnTwistedDataSourced : Bool
    generalizedMoonshineModularitySourced : Bool
    nonFrickeOrbifoldDualitySourced : Bool
    explicit2BTwistedSectorPrecedentSourced : Bool
    localCentralizerTargetAlreadyIndependent : Bool
    badLevelTenTwoValuationSourced : Bool
    twistedTraceValuationAuthoritySpecified : Bool
    twistedTraceValuationAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalGeneralizedMoonshineCentralizerBridgeBoundary :
  GeneralizedMoonshineCentralizerBridgeBoundary
canonicalGeneralizedMoonshineCentralizerBridgeBoundary =
  generalized-moonshine-centralizer-bridge-boundary
    true true true true true false true false true
