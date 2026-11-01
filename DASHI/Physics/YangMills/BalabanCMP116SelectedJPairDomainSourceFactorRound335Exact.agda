{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainSourceFactorRound335Exact where

------------------------------------------------------------------------
-- ROUND335 / FACTOR THE R334 PAIR-DOMAIN WELD AT THE SOURCE BOUNDARY
--
-- R334 correctly blocks the over-coarse implication
--
--   scale/volume common-domain witness
--     => selected physical (J_A,J_B) admissible.
--
-- The CMP116 source text gives a sharper acquisition route: the differentiated
-- terms are taken after passing to one common U,J analytic space.  Therefore
-- the pair-specific R334 payment should not remain an opaque selected-T5 fact.
-- It factors into:
--
--   S1. source alignment: characterize the printed common J-domain strongly
--       enough that any literal source-direction pair in that declared domain
--       is admitted by the proof-bearing CMP116 theorem ABI;
--
--   S2. same-object alignment: the selected physical observable insertions are
--       the literal CMP116/CMP119 J directions on the SAME density.
--
-- This file proves only the compiler S1 -> R334 once a source-domain authority
-- is supplied.  It does not claim S1 or S2.  In particular, bibliographic/source
-- metadata cannot inhabit the authority record.
--
-- Primary source locator:
-- T. Balaban, CMP 116 (1988), Sect. 1 around (1.23)--(1.29): derivatives are
-- represented by Cauchy formula and terms with one localization domain are put
-- on a common domain of analyticity in U,J before summation.
-- DOI: 10.1007/BF01239022.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainWeldRound334Exact as R334

------------------------------------------------------------------------
-- Source-native pair-domain characterization.
--
-- This is intentionally indexed only by the source carrier, not by the T5
-- observable type.  It is the theorem/source-transcription object which R334
-- had previously hidden inside a selected-physical application field.
------------------------------------------------------------------------

record PublishedCMP116CommonJPairDomainAuthority
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    : Set₁ where
  field
    commonDeclaredJDomainAdmitsLiteralSourcePair :
      ∀ scale volume leftJ rightJ →
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        scale volume →
      Source.AdmissibleSourcePair source scale volume leftJ rightJ

open PublishedCMP116CommonJPairDomainAuthority public

------------------------------------------------------------------------
-- Compiler: source-domain theorem -> selected R334 pair weld.
------------------------------------------------------------------------

sourcePairDomainAuthorityBuildsSelectedJPairWeld :
  ∀ {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands} →
  PublishedCMP116CommonJPairDomainAuthority base source demands →
  R334.SelectedJPairCommonDomainWeld base source demands
sourcePairDomainAuthorityBuildsSelectedJPairWeld
    {base = base} authority = record
  { R334.SelectedJPairCommonDomainWeld.commonSourceCoordinateInsideImpliesSelectedPairAdmissible =
      λ cutoff left right commonInside →
        commonDeclaredJDomainAdmitsLiteralSourcePair authority
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right)
          commonInside
  }

------------------------------------------------------------------------
-- Proof-search boundary.
------------------------------------------------------------------------

record Round335Boundary : Set where
  constructor round335-boundary
  field
    selectedPairDomainWeldIndependentPhysicalTheorem : Bool
    selectedPairDomainWeldIndependentPhysicalTheoremIsFalse :
      selectedPairDomainWeldIndependentPhysicalTheorem ≡ false

    commonJPairDomainCharacterizationStillSourceFacing : Bool
    commonJPairDomainCharacterizationStillSourceFacingIsTrue :
      commonJPairDomainCharacterizationStillSourceFacing ≡ true

    literalPhysicalObservableToSourceDirectionStillSameObjectDebt : Bool
    literalPhysicalObservableToSourceDirectionStillSameObjectDebtIsTrue :
      literalPhysicalObservableToSourceDirectionStillSameObjectDebt ≡ true

    commonRadiusExistenceIndependentLeaf : Bool
    commonRadiusExistenceIndependentLeafIsFalse :
      commonRadiusExistenceIndependentLeaf ≡ false

    publishedLocalizationEstimateNeedsReproof : Bool
    publishedLocalizationEstimateNeedsReproofIsFalse :
      publishedLocalizationEstimateNeedsReproof ≡ false

    sourceDomainAuthorityCompilesR334Weld : Bool
    sourceDomainAuthorityCompilesR334WeldIsTrue :
      sourceDomainAuthorityCompilesR334Weld ≡ true

canonicalRound335Boundary : Round335Boundary
canonicalRound335Boundary =
  round335-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl

-- Status is deliberately conditional: the compiler is proved here, but the
-- printed-source/common-J characterization has not been locally replayed into
-- this proof-bearing authority.
round335PublishedCommonJPairDomainAuthorityLevel : ProofLevel
round335PublishedCommonJPairDomainAuthorityLevel = conditional

round335LiteralPhysicalJDirectionMeaningLevel : ProofLevel
round335LiteralPhysicalJDirectionMeaningLevel = Cumulant.literalYMSourceInsertionMeaningLevel

round335CompilerLevel : ProofLevel
round335CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
