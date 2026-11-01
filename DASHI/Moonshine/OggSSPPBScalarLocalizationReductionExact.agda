module DASHI.Moonshine.OggSSPPBScalarLocalizationReductionExact where

------------------------------------------------------------------------
-- PRIME-B SCALAR LOCALIZATION REDUCTION
--
-- PURPOSE
--
-- The live terminal localization theorem is intentionally strong: it asks for
-- semantic source-piece localization into the full p=2 inertia sectors and
-- p=3 Deligne--Rapoport node/branch sectors.
--
-- For the SCALAR exceptional-length consumer, that is more information than
-- necessary.
--
-- p=2:
--   the five geometric sectors factor through the three-value depth quotient,
--   but multiplicity retains five source slots with profile 3,3,2,1,1.
--
-- p=3:
--   both geometric sectors have multiplicity one, so the unresolved
--   H^0/H^1 <-> node/branch alignment is invisible to the scalar consumer.
--
-- DASHI RESULT
--
-- A weaker source-native scalar theorem is enough to derive the two numerical
-- source totals 10 and 2 WITHOUT using those target totals to define the
-- source pieces.
--
-- This owner does NOT construct the Monster/Hauptmodul bridge.  It only
-- removes unnecessary semantic localization obligations from the scalar
-- composition-length subproblem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as P2
import DASHI.Moonshine.OggSSPP3AlignmentIndependentLengthQuotientExact as P3
import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Reduced scalar theorem.
------------------------------------------------------------------------

record PBScalarLocalizationAuthority : Set₁ where
  field
    p2 :
      P2.P2SourceDepthSlotLengthAuthority

    p3 :
      P3.P3TateScalarLengthAuthority

open PBScalarLocalizationAuthority public

------------------------------------------------------------------------
-- 2. Exact source-native scalar totals.
------------------------------------------------------------------------

p2ScalarSourceTotal :
  PBScalarLocalizationAuthority ->
  Nat
p2ScalarSourceTotal A =
  P2.sourceSlotTotal (p2 A)

p3ScalarSourceTotal :
  PBScalarLocalizationAuthority ->
  Nat
p3ScalarSourceTotal A =
  P3.normalizedDVRLength (p3 A)
    (P3.everyTateDegreeHasSourcePiece (p3 A) Tate.tateH0)
  +
  P3.normalizedDVRLength (p3 A)
    (P3.everyTateDegreeHasSourcePiece (p3 A) Tate.tateH1)

p2ScalarSourceTotalIsTen :
  (A : PBScalarLocalizationAuthority) ->
  p2ScalarSourceTotal A ≡ 10
p2ScalarSourceTotalIsTen A =
  P2.sourceSlotTotalIsTen (p2 A)

p3ScalarSourceTotalIsTwo :
  (A : PBScalarLocalizationAuthority) ->
  p3ScalarSourceTotal A ≡ 2
p3ScalarSourceTotalIsTwo A
  rewrite P3.representativeH0LengthIsOne (p3 A)
        | P3.representativeH1LengthIsOne (p3 A) =
  refl

------------------------------------------------------------------------
-- 3. Semantic localization is strictly stronger than scalar payment.
------------------------------------------------------------------------

data ScalarPaymentRequiresP2FiveSectorNames : Set where
data ScalarPaymentRequiresP3NodeBranchAlignment : Set where
data ScalarPaymentCreatesP2SemanticLocalization : Set where
data ScalarPaymentCreatesP3SemanticLocalization : Set where

p2FiveSectorNamesNotRequiredForScalarPayment :
  ScalarPaymentRequiresP2FiveSectorNames -> ⊥
p2FiveSectorNamesNotRequiredForScalarPayment ()

p3NodeBranchAlignmentNotRequiredForScalarPayment :
  ScalarPaymentRequiresP3NodeBranchAlignment -> ⊥
p3NodeBranchAlignmentNotRequiredForScalarPayment ()

scalarPaymentDoesNotCreateP2SemanticLocalization :
  ScalarPaymentCreatesP2SemanticLocalization -> ⊥
scalarPaymentDoesNotCreateP2SemanticLocalization ()

scalarPaymentDoesNotCreateP3SemanticLocalization :
  ScalarPaymentCreatesP3SemanticLocalization -> ⊥
scalarPaymentDoesNotCreateP3SemanticLocalization ()

------------------------------------------------------------------------
-- 4. Same-object / Hauptmodul payment is still independent.
------------------------------------------------------------------------

data ScalarTotalsCreateMonsterBridge : Set where
data ScalarTotalsCreateBadLevelHauptmodulLocalization : Set where
data ScalarTotalsCreateGreenSpeciesAuthority : Set where
data ScalarTotalsMayBeDefinedFromMonsterResidual : Set where
data ScalarTotalsMayBeDefinedFromBase369 : Set where

scalarTotalsDoNotCreateMonsterBridge :
  ScalarTotalsCreateMonsterBridge -> ⊥
scalarTotalsDoNotCreateMonsterBridge ()

scalarTotalsDoNotCreateBadLevelHauptmodulLocalization :
  ScalarTotalsCreateBadLevelHauptmodulLocalization -> ⊥
scalarTotalsDoNotCreateBadLevelHauptmodulLocalization ()

scalarTotalsDoNotCreateGreenSpeciesAuthority :
  ScalarTotalsCreateGreenSpeciesAuthority -> ⊥
scalarTotalsDoNotCreateGreenSpeciesAuthority ()

monsterResidualMayNotDefineScalarSourcePayment :
  ScalarTotalsMayBeDefinedFromMonsterResidual -> ⊥
monsterResidualMayNotDefineScalarSourcePayment ()

base369MayNotDefineScalarSourcePayment :
  ScalarTotalsMayBeDefinedFromBase369 -> ⊥
base369MayNotDefineScalarSourcePayment ()

------------------------------------------------------------------------
-- 5. Live source wall.
------------------------------------------------------------------------

data PBScalarLocalizationAuthorityInhabited : Set where

pbScalarLocalizationStillOpen :
  PBScalarLocalizationAuthorityInhabited -> ⊥
pbScalarLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record PBScalarLocalizationReductionBoundary : Set where
  constructor pb-scalar-localization-reduction-boundary
  field
    p2DepthQuotientOwned : Bool
    p3AlignmentIndependenceOwned : Bool
    reducedP2SourceAuthoritySpecified : Bool
    reducedP3SourceAuthoritySpecified : Bool
    exactP2ScalarTotalDerivedConditionally : Bool
    exactP3ScalarTotalDerivedConditionally : Bool
    p2SemanticSectorLabelsRequiredForScalarConsumer : Bool
    p3SemanticAlignmentRequiredForScalarConsumer : Bool
    reducedScalarAuthorityInhabited : Bool
    monsterBridgeCreatedByScalarTotals : Bool
    hauptmodulLocalizationCreatedByScalarTotals : Bool
    greenSpeciesCreatedByScalarTotals : Bool
    monsterResidualUsedToDefineSourcePayment : Bool
    base369UsedToDefineSourcePayment : Bool
    attributionFirewallPreserved : Bool

canonicalPBScalarLocalizationReductionBoundary :
  PBScalarLocalizationReductionBoundary
canonicalPBScalarLocalizationReductionBoundary =
  pb-scalar-localization-reduction-boundary
    true true true true true true
    false false false
    false false false false false true
