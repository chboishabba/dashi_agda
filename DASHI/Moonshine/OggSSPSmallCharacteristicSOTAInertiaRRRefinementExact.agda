module DASHI.Moonshine.OggSSPSmallCharacteristicSOTAInertiaRRRefinementExact where

------------------------------------------------------------------------
-- SOTA INERTIA-RR REFINEMENT OF THE SMALL-PRIME CORRECTION FRONTIER
--
-- SOURCE / FRAMEWORK INPUT
--
-- Toën-style inertia Riemann--Roch and later explicit quotient-stack formulas
-- decompose local terms by conjugacy/inertia sectors.  A local term depends on
-- more than |C_G(g)|: the action on the tangent/normal representation enters
-- through a factor such as det(1-g), and the sector carries centralizer data.
--
-- Kobin--Zureick-Brown show that the elliptic modular stack in
-- characteristics 2 and 3 is genuinely WILD, with ramification data affecting
-- the modular-form ring.  Therefore the tame inertia formula is not itself the
-- desired Monster-valuation theorem.
--
-- DASHI CONSEQUENCE
--
-- The existing p=2 weight
--
--     v2(|C_G(g)|)
--
-- is retained as a useful finite arithmetic proxy, but it is formally
-- insufficient to determine even the tame character denominator, hence cannot
-- constitute the full wild local term.
--
-- The admissible analytic frontier is refined to require:
--
--   p=2 : sector + centralizer + tangent/character + wild ramification data;
--   p=3 : local branch/node datum + wild bad-level/ramification data;
--   both: an actual q-expansion/cohomological valuation theorem assembling
--         those local data into the exceptional Hauptmodul valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP2CentralizerDepthVsInertiaRRNonfactorabilityExact as P2RR
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as P2Centralizer
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallCharacteristicWildRiemannRochTransferCutsetExact as WildRR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. SOTA source ledger.
------------------------------------------------------------------------

kobinzureickBrown : Source.AttributedSource
kobinzureickBrown =
  Source.mkNoDOISource
    "Andrew Kobin and David Zureick-Brown"
    "Wild Stacky Curves and Rings of Mod p Modular Forms"
    "arXiv:2510.08821"
    "2025"
    "https://arxiv.org/abs/2510.08821"
    Source.academicArticleSource
    "current wild modular-stack source: characteristics 2 and 3 have a unique wild stacky point at j=0 after collision of j=0 and j=1728; wild ramification changes canonical/log-canonical geometry and produces mod-p modular forms not explained by tame lifting. It does not state a Monster-exponent correction formula"
    Source.publicAttribution

dadhwalPankajCharacterTable : Source.AttributedSource
dadhwalPankajCharacterTable =
  Source.mkDOISource
    "Madhu Dadhwal and Pankaj"
    "Group codes over binary tetrahedral group"
    "Journal of Mathematical Cryptology 16(1), 310-319"
    "2022"
    "10.1515/jmc-2022-0009"
    "https://doi.org/10.1515/jmc-2022-0009"
    Source.academicArticleSource
    "explicit binary-tetrahedral conjugacy classes and character table; used to witness equal-centralizer classes with different degree-2 character traces. Not a modular-form or Monster theorem"
    Source.publicAttribution

sotaInertiaRRAtlas : Source.AttributedSourceAtlas
sotaInertiaRRAtlas =
  Source.mkSourceAtlas
    "SOTA inertia-RR / wild modular-stack refinement"
    "DASHI.Moonshine.OggSSPSmallCharacteristicSOTAInertiaRRRefinementExact"
    (dadhwalPankajCharacterTable ∷ kobinzureickBrown ∷ [])
    "external sources justify character dependence and wild modular-stack structure; the cross-weld to the small-prime Monster residual remains DASHI conjectural/recognition work"

------------------------------------------------------------------------
-- 2. The current preferred p2 proxy forgets character information.
------------------------------------------------------------------------

preferredP2WeightOnRawClass :
  P2Inertia.BinaryTetrahedralConjugacyClass ->
  Nat
preferredP2WeightOnRawClass class =
  Preferred.p2Weight (P2Inertia.quotientByInversion class)

preferredWeightSameOnCollision :
  preferredP2WeightOnRawClass P2RR.orderThreeRepresentative
  ≡
  preferredP2WeightOnRawClass P2RR.orderSixRepresentative
preferredWeightSameOnCollision = refl

preferredWeightCannotDetermineTameCharacterDenominator :
  NF.FactorsThrough
    preferredP2WeightOnRawClass
    P2RR.tameDetOneDenominatorMagnitude
  ->
  ⊥
preferredWeightCannotDetermineTameCharacterDenominator factor =
  NF.witnessRulesOutEveryFlatFactorisation witness factor
  where
    witness :
      NF.NonFactorabilityWitness
        preferredP2WeightOnRawClass
        P2RR.tameDetOneDenominatorMagnitude
    witness =
      NF.nonFactorabilityWitness
        P2RR.orderThreeRepresentative
        P2RR.orderSixRepresentative
        preferredWeightSameOnCollision
        P2RR.differentTameDenominator

------------------------------------------------------------------------
-- 3. Refined p2 wild local datum.
------------------------------------------------------------------------

record P2CharacterAwareWildLocalDatum : Set where
  constructor p2-character-aware-wild-local-datum
  field
    sector :
      P2Inertia.BinaryTetrahedralInversionOrbit

    representative :
      P2Inertia.BinaryTetrahedralConjugacyClass

    centralizerOrder :
      Nat

    centralizerTwoAdicDepth :
      Nat

    characterTrace :
      P2RR.DegreeTwoTrace

    tameDenominatorMagnitude :
      Nat

    wildRamificationDepth :
      Nat

open P2CharacterAwareWildLocalDatum public

p2DatumFromRepresentative :
  (class : P2Inertia.BinaryTetrahedralConjugacyClass) ->
  Nat ->
  P2CharacterAwareWildLocalDatum
p2DatumFromRepresentative class wildDepth =
  p2-character-aware-wild-local-datum
    (P2Inertia.quotientByInversion class)
    class
    (P2Centralizer.centralizerOrder class)
    (P2Centralizer.centralizerTwoAdicDepth class)
    (P2RR.degreeTwoTrace class)
    (P2RR.tameDetOneDenominatorMagnitude class)
    wildDepth

------------------------------------------------------------------------
-- 4. Refined p3 local datum.
------------------------------------------------------------------------

record P3BranchAwareWildLocalDatum : Set where
  constructor p3-branch-aware-wild-local-datum
  field
    localOrbit :
      P3.P3LocalOrbit

    branchSensitive :
      Bool

    wildRamificationDepth :
      Nat

    badLevelDepth :
      Nat

open P3BranchAwareWildLocalDatum public

------------------------------------------------------------------------
-- 5. Strong analytic authority: no count/proxy shortcut.
------------------------------------------------------------------------

record SOTACharacterAwareWildValuationAuthority : Set₁ where
  field
    AnalyticLocalTerm : Set

    p2Datum :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      P2CharacterAwareWildLocalDatum

    p3Datum :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      P3BranchAwareWildLocalDatum

    p2AnalyticTerm :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      AnalyticLocalTerm

    p3AnalyticTerm :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      AnalyticLocalTerm

    valuationMultiplicity :
      AnalyticLocalTerm ->
      Nat

    p2ProxyWeightRecoveredFromActualLocalTerm :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      Preferred.weight Preferred.p2PreferredPresentation sector
      ≡ valuationMultiplicity (p2AnalyticTerm sector)

    p3ProxyWeightRecoveredFromActualLocalTerm :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      Preferred.weight Preferred.p3PreferredPresentation sector
      ≡ valuationMultiplicity (p3AnalyticTerm sector)

    p2CharacterCoordinateActuallyUsed :
      Bool
    p2CharacterCoordinateActuallyUsedIsTrue :
      p2CharacterCoordinateActuallyUsed ≡ true

    p2WildRamificationActuallyUsed :
      Bool
    p2WildRamificationActuallyUsedIsTrue :
      p2WildRamificationActuallyUsed ≡ true

    p3BranchCoordinateActuallyUsed :
      Bool
    p3BranchCoordinateActuallyUsedIsTrue :
      p3BranchCoordinateActuallyUsed ≡ true

    p3WildRamificationActuallyUsed :
      Bool
    p3WildRamificationActuallyUsedIsTrue :
      p3WildRamificationActuallyUsed ≡ true

    localTermsAssembleIntoCorrectedHauptmodulValuation :
      Bool
    localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue :
      localTermsAssembleIntoCorrectedHauptmodulValuation ≡ true

open SOTACharacterAwareWildValuationAuthority public

------------------------------------------------------------------------
-- 6. Adapter to the existing preferred correction authority.
------------------------------------------------------------------------

asPreferredCorrectedValuationAuthority :
  SOTACharacterAwareWildValuationAuthority ->
  Preferred.PreferredCorrectedValuationAuthority
asPreferredCorrectedValuationAuthority A =
  record
    { Preferred.AnalyticLocalTerm =
        AnalyticLocalTerm A
    ; Preferred.p2AnalyticTerm =
        p2AnalyticTerm A
    ; Preferred.p3AnalyticTerm =
        p3AnalyticTerm A
    ; Preferred.analyticMultiplicity =
        valuationMultiplicity A
    ; Preferred.p2WeightsAreActualLocalValuations =
        p2ProxyWeightRecoveredFromActualLocalTerm A
    ; Preferred.p3WeightsAreActualLocalValuations =
        p3ProxyWeightRecoveredFromActualLocalTerm A
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuation =
        localTermsAssembleIntoCorrectedHauptmodulValuation A
    ; Preferred.localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue =
        localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue A
    ; Preferred.correctedValuationPaysDuncanSwisherP2Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP2GapIsTrue =
        refl
    ; Preferred.correctedValuationPaysDuncanSwisherP3Gap =
        true
    ; Preferred.correctedValuationPaysDuncanSwisherP3GapIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 7. Promotion firewalls.
------------------------------------------------------------------------

data CentralizerDepthProxyIsSOTAInertiaRRWeight : Set where
data TameCharacterFormulaClosesWildPrime : Set where
data CharacterTableCreatesMonsterValuation : Set where
data SOTARefinementAlreadyInhabited : Set where

centralizerDepthProxyIsNotSOTAInertiaRRWeight :
  CentralizerDepthProxyIsSOTAInertiaRRWeight -> ⊥
centralizerDepthProxyIsNotSOTAInertiaRRWeight ()

tameCharacterFormulaDoesNotCloseWildPrime :
  TameCharacterFormulaClosesWildPrime -> ⊥
tameCharacterFormulaDoesNotCloseWildPrime ()

characterTableDoesNotCreateMonsterValuation :
  CharacterTableCreatesMonsterValuation -> ⊥
characterTableDoesNotCreateMonsterValuation ()

sotaRefinementStillOpen :
  SOTARefinementAlreadyInhabited -> ⊥
sotaRefinementStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SOTAInertiaRRRefinementBoundary : Set where
  constructor sota-inertia-rr-refinement-boundary
  field
    p2CharacterTableExternallySourced : Bool
    p2PreferredProxyCollisionWitnessed : Bool
    p2PreferredProxyDeterminesTameDenominator : Bool
    p2CharacterAwareWildDatumSpecified : Bool
    p3BranchAwareWildDatumSpecified : Bool
    wildRamificationRequiredAtBothPrimes : Bool
    adapterToPreferredAuthorityOwned : Bool
    tameRRPromotedToWildValuation : Bool
    correctedHauptmodulAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalSOTAInertiaRRRefinementBoundary :
  SOTAInertiaRRRefinementBoundary
canonicalSOTAInertiaRRRefinementBoundary =
  sota-inertia-rr-refinement-boundary
    true true false true true true true false false true
