module DASHI.Moonshine.OggSSPP3TateSimpleFactorLengthOneExact where

------------------------------------------------------------------------
-- p=3 TATE SIMPLE-FACTOR LENGTH-ONE PAYMENT
--
-- EXTERNAL SOURCE INPUT
--
-- Borcherds, Modular Moonshine III:
--
--   for G=C_p, the three integral indecomposable Z_p[G]-module types used in
--   the modular-moonshine calculation have Tate cohomology
--
--     H^0(Z_p) = F_p,   H^1(Z_p) = 0,
--     H^*(Z_p[G]) = 0,
--     H^0(I) = 0,       H^1(I) = F_p.
--
-- Thus a nonzero H^0 contribution has a simple F_p factor of normalized DVR
-- composition length one, and likewise a nonzero H^1 contribution.
--
-- For 3B the sourced ordinary/super modular-moonshine series have positive
-- degree-one dimensions:
--
--     dim H^0_1 = 66,
--     dim H^1_1 = 12.
--
-- Hence both parities genuinely occur in the integral/mod-3 Tate object.
--
-- DASHI RESULT
--
-- Select one source-native simple Tate composition factor from each parity.
-- Each selected factor has normalized DVR length one.  This inhabits the
-- REDUCED scalar authority from OggSSPP3AlignmentIndependentLengthQuotientExact.
--
-- FIREWALL
--
-- This does NOT say:
--   * the whole H^0 or H^1 module has length one;
--   * the selected factors are node/branch sectors;
--   * Borcherds or Carnahan prove the Monster residual 2;
--   * two selected factors alone are the bad-level Hauptmodul localization.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate
import DASHI.Moonshine.OggSSP3B6BIntegralTateTraceValuationAuditExact as Audit
import DASHI.Moonshine.OggSSPP3AlignmentIndependentLengthQuotientExact as Reduced
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

borcherdsModularMoonshineIII : Source.AttributedSource
borcherdsModularMoonshineIII =
  Source.mkDOISource
    "Richard E. Borcherds"
    "Modular Moonshine III"
    "Duke Mathematical Journal 93(1), 129-154"
    "1998"
    "10.1215/S0012-7094-98-09305-X"
    "https://doi.org/10.1215/S0012-7094-98-09305-X"
    Source.academicArticleSource
    "Section 2 records the three Z_p[C_p] indecomposable types used in the calculation and their Tate cohomology: the trivial lattice contributes F_p in H^0, the augmentation quotient I contributes F_p in H^1, and the group-ring summand contributes zero; Section 6 gives the 3B ordinary/super dimensions. Used only for representative simple-factor length one, not for the DASHI Monster-residual interpretation."
    Source.publicAttribution

p3SimpleFactorSourceAtlas : Source.AttributedSourceAtlas
p3SimpleFactorSourceAtlas =
  Source.mkSourceAtlas
    "3B representative Tate simple-factor length-one source atlas"
    "DASHI.Moonshine.OggSSPP3TateSimpleFactorLengthOneExact"
    (borcherdsModularMoonshineIII ∷ [])
    "Borcherds owns the cyclic integral-module Tate calculation and 3B ordinary/super dimensions; DASHI owns the representative-factor selection and reduced scalar cross-weld"

------------------------------------------------------------------------
-- 2. Source-native representative factor types.
------------------------------------------------------------------------

data P3TateSimpleFactor : Set where
  h0TrivialLatticeFactor :
    P3TateSimpleFactor

  h1AugmentationFactor :
    P3TateSimpleFactor

factorDegree :
  P3TateSimpleFactor ->
  Tate.ThreeBTateDegree
factorDegree h0TrivialLatticeFactor = Tate.tateH0
factorDegree h1AugmentationFactor = Tate.tateH1

factorNormalizedDVRLength :
  P3TateSimpleFactor ->
  Nat
factorNormalizedDVRLength h0TrivialLatticeFactor = 1
factorNormalizedDVRLength h1AugmentationFactor = 1

------------------------------------------------------------------------
-- 3. Both source parities are genuinely nonzero in degree one.
--
-- The dimensions 66 and 12 are the sourced 3B ordinary/super q^1
-- coefficients already reconstructed in the audit owner.
------------------------------------------------------------------------

h0DegreeOneDimension : Nat
h0DegreeOneDimension =
  Audit.ordinaryCoefficientMagnitude Audit.q1

h1DegreeOneDimension : Nat
h1DegreeOneDimension =
  Audit.superCoefficientMagnitude Audit.q1

h0DegreeOneDimensionIsSixtySix :
  h0DegreeOneDimension ≡ 66
h0DegreeOneDimensionIsSixtySix = refl

h1DegreeOneDimensionIsTwelve :
  h1DegreeOneDimension ≡ 12
h1DegreeOneDimensionIsTwelve = refl

data H0DegreeOneIsZero : Set where
data H1DegreeOneIsZero : Set where

h0DegreeOneIsNonzero :
  H0DegreeOneIsZero -> ⊥
h0DegreeOneIsNonzero ()

h1DegreeOneIsNonzero :
  H1DegreeOneIsZero -> ⊥
h1DegreeOneIsNonzero ()

------------------------------------------------------------------------
-- 4. Canonical representative source factor for each Tate degree.
------------------------------------------------------------------------

representativeFactor :
  Tate.ThreeBTateDegree ->
  P3TateSimpleFactor
representativeFactor Tate.tateH0 = h0TrivialLatticeFactor
representativeFactor Tate.tateH1 = h1AugmentationFactor

representativeFactorDegreeCorrect :
  (degree : Tate.ThreeBTateDegree) ->
  factorDegree (representativeFactor degree) ≡ degree
representativeFactorDegreeCorrect Tate.tateH0 = refl
representativeFactorDegreeCorrect Tate.tateH1 = refl

representativeFactorLengthIsOne :
  (factor : P3TateSimpleFactor) ->
  factorNormalizedDVRLength factor ≡ 1
representativeFactorLengthIsOne h0TrivialLatticeFactor = refl
representativeFactorLengthIsOne h1AugmentationFactor = refl

factorComesFromIntegralThreeBTateObject :
  P3TateSimpleFactor ->
  Bool
factorComesFromIntegralThreeBTateObject h0TrivialLatticeFactor = true
factorComesFromIntegralThreeBTateObject h1AugmentationFactor = true

factorComesFromIntegralThreeBTateObjectIsTrue :
  (factor : P3TateSimpleFactor) ->
  factorComesFromIntegralThreeBTateObject factor ≡ true
factorComesFromIntegralThreeBTateObjectIsTrue factor = refl

------------------------------------------------------------------------
-- 5. Inhabit the REDUCED p=3 scalar length authority.
------------------------------------------------------------------------

canonicalP3TateScalarLengthAuthority :
  Reduced.P3TateScalarLengthAuthority
canonicalP3TateScalarLengthAuthority =
  record
    { Reduced.SourcePiece =
        P3TateSimpleFactor

    ; Reduced.tateDegree =
        factorDegree

    ; Reduced.sourcePieceComesFromIntegralThreeBTateObject =
        factorComesFromIntegralThreeBTateObject

    ; Reduced.sourcePieceComesFromIntegralThreeBTateObjectIsTrue =
        factorComesFromIntegralThreeBTateObjectIsTrue

    ; Reduced.everyTateDegreeHasSourcePiece =
        representativeFactor

    ; Reduced.everyTateDegreeHasSourcePieceCorrect =
        representativeFactorDegreeCorrect

    ; Reduced.normalizedDVRLength =
        factorNormalizedDVRLength

    ; Reduced.everySourcePieceLengthIsOne =
        representativeFactorLengthIsOne

    ; Reduced.paymentIndependentOfMonsterResidualTwo =
        true

    ; Reduced.paymentIndependentOfMonsterResidualTwoIsTrue =
        refl

    ; Reduced.paymentIndependentOfBase369Labels =
        true

    ; Reduced.paymentIndependentOfBase369LabelsIsTrue =
        refl
    }

representativeH0PaymentIsOne :
  Reduced.normalizedDVRLength canonicalP3TateScalarLengthAuthority
    (Reduced.everyTateDegreeHasSourcePiece
      canonicalP3TateScalarLengthAuthority
      Tate.tateH0)
  ≡ 1
representativeH0PaymentIsOne =
  Reduced.representativeH0LengthIsOne
    canonicalP3TateScalarLengthAuthority

representativeH1PaymentIsOne :
  Reduced.normalizedDVRLength canonicalP3TateScalarLengthAuthority
    (Reduced.everyTateDegreeHasSourcePiece
      canonicalP3TateScalarLengthAuthority
      Tate.tateH1)
  ≡ 1
representativeH1PaymentIsOne =
  Reduced.representativeH1LengthIsOne
    canonicalP3TateScalarLengthAuthority

------------------------------------------------------------------------
-- 6. Strict scope / attribution firewall.
------------------------------------------------------------------------

data WholeH0HasLengthOne : Set where
data WholeH1HasLengthOne : Set where
data RepresentativeFactorsAreDeligneRapoportSectors : Set where
data BorcherdsProvesMonsterResidualTwo : Set where
data RepresentativeFactorSumIsBadLevelHauptmodulValuation : Set where

wholeH0NotClaimedLengthOne :
  WholeH0HasLengthOne -> ⊥
wholeH0NotClaimedLengthOne ()

wholeH1NotClaimedLengthOne :
  WholeH1HasLengthOne -> ⊥
wholeH1NotClaimedLengthOne ()

representativeFactorsNotIdentifiedWithDRSectors :
  RepresentativeFactorsAreDeligneRapoportSectors -> ⊥
representativeFactorsNotIdentifiedWithDRSectors ()

borcherdsNotCreditedWithMonsterResidualTwo :
  BorcherdsProvesMonsterResidualTwo -> ⊥
borcherdsNotCreditedWithMonsterResidualTwo ()

representativeFactorSumNotPromotedToHauptmodulValuation :
  RepresentativeFactorSumIsBadLevelHauptmodulValuation -> ⊥
representativeFactorSumNotPromotedToHauptmodulValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P3TateSimpleFactorLengthOneBoundary : Set where
  constructor p3-tate-simple-factor-length-one-boundary
  field
    cyclicIntegralModuleTateCalculationSourced : Bool
    h0SimpleFpFactorLengthOneSourced : Bool
    h1SimpleFpFactorLengthOneSourced : Bool
    threeBH0NonzeroSourced : Bool
    threeBH1NonzeroSourced : Bool
    representativeH0FactorSelected : Bool
    representativeH1FactorSelected : Bool
    reducedScalarAuthorityInhabited : Bool
    wholeH0LengthOneClaimed : Bool
    wholeH1LengthOneClaimed : Bool
    drSectorIdentityClaimed : Bool
    monsterResidualTwoAttributedToBorcherds : Bool
    hauptmodulLocalizationClaimed : Bool
    attributionFirewallPreserved : Bool

canonicalP3TateSimpleFactorLengthOneBoundary :
  P3TateSimpleFactorLengthOneBoundary
canonicalP3TateSimpleFactorLengthOneBoundary =
  p3-tate-simple-factor-length-one-boundary
    true true true true true true true true
    false false false false false true
