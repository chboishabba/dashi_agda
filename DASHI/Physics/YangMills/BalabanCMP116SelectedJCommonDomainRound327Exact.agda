{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJCommonDomainRound327Exact where

------------------------------------------------------------------------
-- ROUND327 / SELECTED-J COMMON-DOMAIN COMPILER
--
-- R326 leaves one selected-J applicability package as the source-facing H1
-- residual.  The older R103/R104/R114 chain already proves something stronger
-- than an opaque membership receipt once the literal CMP116 finite normalized
-- demands are known:
--
--   finite source demands
--     -> canonical positive common radius
--     -> SourceCoordinateInside at every selected scale/volume.
--
-- Therefore membership of the selected J pair in the common source domain is
-- compiler-owned PROVIDED the selected physical J directions have already been
-- identified with CMP116's source-coordinate carrier.  The remaining physical
-- seam is that same-object/source-coordinate identification and the application
-- of the published localization theorem on that carrier; it is not a separate
-- radius-existence or pair-membership theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322

record SelectedJCommonDomainLocalization
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    demands : R104.CMP116FiniteNormalizedAnalyticDemands

    -- Source theorem specialized only as far as the common source-domain
    -- predicate.  The domain witness itself is generated below from R114.
    localizedOnCommonSourceDomain :
      ∀ cutoff left right →
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff) →
      R278.magnitude extension
        (Cumulant.mixedSecondLogDerivative (R318.calculus base)
          left right cutoff)
      ≤ Shell.rootedShell (R318.shellData base)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right)

open SelectedJCommonDomainLocalization public

selectedJSourceCoordinateInside :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  (source : SelectedJCommonDomainLocalization base) →
  ∀ cutoff left right →
  Common.SourceCoordinateInside
    (R114.canonicalCMP116CommonDomain
      {R318.Scale base} {R318.Volume base} (demands source))
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)
selectedJSourceCoordinateInside {base = base} source cutoff left right =
  Common.sourceCoordinateInside
    (R114.canonicalCMP116CommonDomain
      {R318.Scale base} {R318.Volume base} (demands source))
    (R318.scaleOf base cutoff)
    (R318.volumeOf base cutoff)

commonDomainLocalizationBuildsR320Payment :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  SelectedJCommonDomainLocalization base →
  R320.DirectSelectedT5MarkedDecayPayment base
commonDomainLocalizationBuildsR320Payment source = record
  { R320.DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell =
      λ cutoff left right →
        localizedOnCommonSourceDomain source cutoff left right
          (selectedJSourceCoordinateInside source cutoff left right)
  }

-- Compatibility with R322: choose the admissibility predicate to be exactly
-- the canonical CMP116 source-domain predicate.  Its selected inhabitant is
-- then produced by R114; no separate pair-admissibility theorem is required.
commonDomainLocalizationBuildsR322Application :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  SelectedJCommonDomainLocalization base →
  R322.CMP116SelectedJDomainApplication base
commonDomainLocalizationBuildsR322Application {base = base} source = record
  { R322.CMP116SelectedJDomainApplication.AdmissibleSelectedJPair =
      λ cutoff left right →
        Common.SourceCoordinateInside
          (R114.canonicalCMP116CommonDomain
            {R318.Scale base} {R318.Volume base} (demands source))
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
  ; R322.CMP116SelectedJDomainApplication.selectedJPairAdmissible =
      selectedJSourceCoordinateInside source
  ; R322.CMP116SelectedJDomainApplication.publishedDifferentiatedLocalization =
      localizedOnCommonSourceDomain source
  }

record Round327Boundary : Set where
  constructor round327-boundary
  field
    positiveCommonRadiusNeedsIndependentExistenceProof : Bool
    positiveCommonRadiusNeedsIndependentExistenceProofIsFalse :
      positiveCommonRadiusNeedsIndependentExistenceProof ≡ false

    selectedJPairMembershipNeedsIndependentProofAfterDemandInstantiation : Bool
    selectedJPairMembershipNeedsIndependentProofAfterDemandInstantiationIsFalse :
      selectedJPairMembershipNeedsIndependentProofAfterDemandInstantiation ≡ false

    finiteDemandExtractionStillSourceFacing : Bool
    finiteDemandExtractionStillSourceFacingIsTrue :
      finiteDemandExtractionStillSourceFacing ≡ true

    selectedPhysicalJEqualsCMP116SourceCoordinateStillSameObjectDebt : Bool
    selectedPhysicalJEqualsCMP116SourceCoordinateStillSameObjectDebtIsTrue :
      selectedPhysicalJEqualsCMP116SourceCoordinateStillSameObjectDebt ≡ true

    publishedLocalizationApplicationStillRequired : Bool
    publishedLocalizationApplicationStillRequiredIsTrue :
      publishedLocalizationApplicationStillRequired ≡ true

    commonDomainPackageCompilesDirectlyToR320 : Bool
    commonDomainPackageCompilesDirectlyToR320IsTrue :
      commonDomainPackageCompilesDirectlyToR320 ≡ true

canonicalRound327Boundary : Round327Boundary
canonicalRound327Boundary =
  round327-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl

round327CommonRadiusCompilerLevel : ProofLevel
round327CommonRadiusCompilerLevel = R114.cmp116FiniteDemandsToCommonRadiusObjectLevel

round327FiniteDemandExtractionLevel : ProofLevel
round327FiniteDemandExtractionLevel = R104.literalCMP116FiniteNormalizedDemandExtractionLevel

round327SelectedJCommonDomainCompilerLevel : ProofLevel
round327SelectedJCommonDomainCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
