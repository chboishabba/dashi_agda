{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact where

------------------------------------------------------------------------
-- ROUND322 / CMP116 SELECTED-J DOMAIN APPLICATION
--
-- R320 gives the least-privilege H1 consumer on the exact selected T5 carrier.
-- R290 identifies the correct source family: CMP116's declared analytic J
-- directions, not CMP109's vacuum-polarization field Hessian.
--
-- This owner separates:
--   * SOURCE THEOREM: differentiated localization for every admissible declared
--     CMP116 J pair on the selected shell carrier;
--   * PHYSICAL APPLICATION: the literal selected T5 observable directions are
--     admissible members of that same J domain, uniformly in cutoff/volume.
--
-- Once those two coordinates are supplied, R320's single analytic field is
-- compiler output.  No CMP109 Pi = connected-cumulant identification is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

record CMP116SelectedJDomainApplication
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    AdmissibleSelectedJPair :
      (cutoff : Agda.Builtin.Nat.Nat) → TestObservable → TestObservable → Set

    selectedJPairAdmissible :
      ∀ cutoff left right → AdmissibleSelectedJPair cutoff left right

    -- Source theorem on the declared CMP116 J-domain, already specialized to
    -- the exact selected shell/root/distance carrier.  This is source authority,
    -- not a newly proved DASHI analytic estimate.
    publishedDifferentiatedLocalization :
      ∀ cutoff left right →
      AdmissibleSelectedJPair cutoff left right →
      R278.magnitude extension
        (Cumulant.mixedSecondLogDerivative (R318.calculus base)
          left right cutoff)
      ≤ Shell.rootedShell (R318.shellData base)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right)

open CMP116SelectedJDomainApplication public

selectedJDomainApplicationBuildsR320Payment :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  CMP116SelectedJDomainApplication base →
  R320.DirectSelectedT5MarkedDecayPayment base
selectedJDomainApplicationBuildsR320Payment application = record
  { R320.DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell =
      λ cutoff left right →
        publishedDifferentiatedLocalization application cutoff left right
          (selectedJPairAdmissible application cutoff left right)
  }

------------------------------------------------------------------------
-- WrongType / proof-search boundary.
------------------------------------------------------------------------

cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulant : Bool
cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulant = false

cmp116JDomainIsCorrectSourceFamilyForR320 : Bool
cmp116JDomainIsCorrectSourceFamilyForR320 = true

publishedDifferentiatedLocalizationIsNewYMAnalysis : Bool
publishedDifferentiatedLocalizationIsNewYMAnalysis = false

selectedJDomainApplicabilityStillPhysical : Bool
selectedJDomainApplicabilityStillPhysical = true

r320PaymentAfterSourceAndApplicabilityIsCompiler : Bool
r320PaymentAfterSourceAndApplicabilityIsCompiler = true

clayPromotion : Bool
clayPromotion = false

cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulantIsFalse :
  cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulant ≡ false
cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulantIsFalse = refl

cmp116JDomainIsCorrectSourceFamilyForR320IsTrue :
  cmp116JDomainIsCorrectSourceFamilyForR320 ≡ true
cmp116JDomainIsCorrectSourceFamilyForR320IsTrue = refl

publishedDifferentiatedLocalizationIsNewYMAnalysisIsFalse :
  publishedDifferentiatedLocalizationIsNewYMAnalysis ≡ false
publishedDifferentiatedLocalizationIsNewYMAnalysisIsFalse = refl

selectedJDomainApplicabilityStillPhysicalIsTrue :
  selectedJDomainApplicabilityStillPhysical ≡ true
selectedJDomainApplicabilityStillPhysicalIsTrue = refl

r320PaymentAfterSourceAndApplicabilityIsCompilerIsTrue :
  r320PaymentAfterSourceAndApplicabilityIsCompiler ≡ true
r320PaymentAfterSourceAndApplicabilityIsCompilerIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

cmp116DifferentiatedLocalizationSourceLevel : ProofLevel
cmp116DifferentiatedLocalizationSourceLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

selectedJDomainApplicabilityLevel : ProofLevel
selectedJDomainApplicabilityLevel = conditional

round322ApplicationCompilerLevel : ProofLevel
round322ApplicationCompilerLevel = machineChecked
