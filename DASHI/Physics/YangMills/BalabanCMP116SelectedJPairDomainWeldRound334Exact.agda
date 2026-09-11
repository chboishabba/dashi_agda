{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJPairDomainWeldRound334Exact where

------------------------------------------------------------------------
-- ROUND334 / COMMON-RADIUS MEMBERSHIP != SELECTED J-PAIR ADMISSIBILITY
--
-- R327 used the canonical common-radius `SourceCoordinateInside` predicate as a
-- sufficient selected-J admissibility carrier.  Source archaeology shows why a
-- proof-bearing bridge must remain explicit: CMP116's differentiated theorem is
-- stated on an admissible PAIR of literal J/source directions, whereas the R103
-- common-radius predicate is indexed only by scale and volume.
--
-- Therefore the current least-privilege H1 application seam is:
--
--   canonical common source-domain membership
--     + SAME-OBJECT pair-domain weld for the selected literal J_A,J_B
--     ---------------------------------------------------------------
--       PublishedCMP116DifferentiatedLocalization.AdmissibleSourcePair
--
-- This module creates no new localization estimate.  It only prevents an
-- over-coarse scale/volume predicate from silently manufacturing pair-specific
-- source applicability.
--
-- Primary source:
-- Tadeusz Balaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
--  Cluster Expansions", CMP 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
-- Source locator: Sect. 1, differentiated/Cauchy representation (1.23), common
-- analytic J-domain preceding it, and exponential localization sum (1.29).
--
-- DOI/QID/Dewey/OEIS/source metadata are navigation/provenance only; none can
-- inhabit the proof field below.
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
import DASHI.Physics.YangMills.BalabanCMP116PublishedAuthoritySelectedT5ApplicationExact as Application

record SelectedJPairCommonDomainWeld
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
    -- This is the actual same-object/application theorem.  It may be proved
    -- from literal source-norm bounds, normalized selected insertions, or a
    -- stronger source-domain theorem; this ABI does not prescribe the tactic.
    commonSourceCoordinateInsideImpliesSelectedPairAdmissible :
      ∀ cutoff left right →
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff) →
      Source.AdmissibleSourcePair source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)

open SelectedJPairCommonDomainWeld public

selectedPairAdmissibleFromCommonDomain :
  ∀ {Measure TestObservable}
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
  SelectedJPairCommonDomainWeld base source demands →
  ∀ cutoff left right →
  Source.AdmissibleSourcePair source
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
    (Cumulant.sourceDirectionOf (R318.meaning base) left)
    (Cumulant.sourceDirectionOf (R318.meaning base) right)
selectedPairAdmissibleFromCommonDomain
    {base = base} {demands = demands} weld cutoff left right =
  commonSourceCoordinateInsideImpliesSelectedPairAdmissible weld cutoff left right
    (Common.sourceCoordinateInside
      (R114.canonicalCMP116CommonDomain
        {R318.Scale base} {R318.Volume base} demands)
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff))

record SelectedT5CMP116ApplicationFromCommonDomain
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
    (domainWeld : SelectedJPairCommonDomainWeld base source demands)
    : Set₁ where
  field
    sourceOrderToRational : ∀ {left right} →
      Source.LessEqual source left right → left ℚ.≤ right

    sourceMagnitudeIsSelectedMagnitude : ∀ cutoff left right →
      Source.differentiatedMagnitude source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative
          (R318.meaning base)
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right)
          cutoff)

    sourceEnvelopeBelowSelectedRootedShell : ∀ cutoff left right →
      Source.sourceEnvelope source
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (Source.sourceRoot source
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right))
        (Source.sourceDistance source
          (Cumulant.sourceDirectionOf (R318.meaning base) left)
          (Cumulant.sourceDirectionOf (R318.meaning base) right))
      ℚ.≤
      DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.rootedShell
        (R318.shellData base)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right)

open SelectedT5CMP116ApplicationFromCommonDomain public

asPublishedAuthorityApplication :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {source : Source.PublishedCMP116DifferentiatedLocalization
      (R318.Scale base)
      (R318.Volume base)
      (R318.Root base)
      (R318.SourceDirection base)
      ℚ}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {domainWeld : SelectedJPairCommonDomainWeld base source demands} →
  SelectedT5CMP116ApplicationFromCommonDomain base source demands domainWeld →
  Application.SelectedT5CMP116AuthorityApplication base source
asPublishedAuthorityApplication
    {domainWeld = domainWeld} application = record
  { Application.SelectedT5CMP116AuthorityApplication.sourceOrderToRational =
      sourceOrderToRational application
  ; Application.SelectedT5CMP116AuthorityApplication.selectedPairAdmissible =
      selectedPairAdmissibleFromCommonDomain domainWeld
  ; Application.SelectedT5CMP116AuthorityApplication.sourceMagnitudeIsSelectedMagnitude =
      sourceMagnitudeIsSelectedMagnitude application
  ; Application.SelectedT5CMP116AuthorityApplication.sourceEnvelopeBelowSelectedRootedShell =
      sourceEnvelopeBelowSelectedRootedShell application
  }

record Round334Boundary : Set where
  constructor round334-boundary
  field
    scaleVolumeCommonDomainAloneProvesSelectedPairAdmissible : Bool
    scaleVolumeCommonDomainAloneProvesSelectedPairAdmissibleIsFalse :
      scaleVolumeCommonDomainAloneProvesSelectedPairAdmissible ≡ false

    pairSpecificDomainWeldRequired : Bool
    pairSpecificDomainWeldRequiredIsTrue : pairSpecificDomainWeldRequired ≡ true

    commonRadiusExistenceNeedsReproof : Bool
    commonRadiusExistenceNeedsReproofIsFalse : commonRadiusExistenceNeedsReproof ≡ false

    publishedLocalizationNeedsReproof : Bool
    publishedLocalizationNeedsReproofIsFalse : publishedLocalizationNeedsReproof ≡ false

    doiQidDeweyOeisCanPayDomainWeld : Bool
    doiQidDeweyOeisCanPayDomainWeldIsFalse : doiQidDeweyOeisCanPayDomainWeld ≡ false

canonicalRound334Boundary : Round334Boundary
canonicalRound334Boundary =
  round334-boundary false refl true refl false refl false refl false refl

round334PairSpecificDomainWeldLevel : ProofLevel
round334PairSpecificDomainWeldLevel = conditional

round334ApplicationCompilerLevel : ProofLevel
round334ApplicationCompilerLevel = machineChecked
