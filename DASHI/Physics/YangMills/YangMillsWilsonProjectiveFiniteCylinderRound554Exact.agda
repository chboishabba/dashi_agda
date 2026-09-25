{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonProjectiveFiniteCylinderRound554Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND554:
-- WILSON PATH LOCALITY -> FINITE PROJECTIVE CYLINDER FUNCTION
--
-- Give "finite-cylinder" its concrete meaning on the preferred Wilson lane:
--
--   F is finite-cylinder
--     iff there is a finite cutoff whose configuration projection determines F.
--
-- R529 already proves a Wilson observable is determined by the edge values on
-- its finite closed path.  Hence the only YM-specific bridge is:
--
--   some projective cutoff captures every edge on that selected path.
--
-- Once that capture theorem is supplied, the selected Wilson observable is a
-- finite-cylinder function.  R553 then turns standard projective convergence
-- plus scalar-limit uniqueness into
--
--   limitExpectation(W) = integral W dmu.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFromStructuralRound530Exact as R530
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFamilyRound529Exact as R529
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
import DASHI.Physics.YangMills.YangMillsSelectedCylinderFunctionClosureRound553Exact as R553
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ProjectiveConfigurationProjection
    (Configuration : Set) : Set₁ where
  field
    FiniteConfiguration : Nat → Set
    project : Nat → Configuration → FiniteConfiguration

open ProjectiveConfigurationProjection public

record FiniteProjectionSupport
    {Configuration : Set}
    (projection : ProjectiveConfigurationProjection Configuration)
    (observable : Configuration → ℝ)
    : Set where
  field
    cutoff : Nat
    determinedByCutoff :
      ∀ left right →
      project projection cutoff left ≡ project projection cutoff right →
      observable left ≡ observable right

open FiniteProjectionSupport public

record WilsonProjectiveCapture
    (G X Configuration Position : Set)
    (structural : Structural.StructuralSourceBundle G X)
    (wilson :
      R530.StructuralWilsonLocalData
        G X Configuration Position structural)
    (projection : ProjectiveConfigurationProjection Configuration)
    : Set₁ where
  field
    cutoffFor : G → Position → Nat

    projectionAgreementImpliesPathAgreement :
      ∀ group position left right →
      project projection (cutoffFor group position) left
      ≡ project projection (cutoffFor group position) right →
      R529.AgreesOnPath
        (R530.decode wilson group left)
        (R530.decode wilson group right)
        (R530.boundaryAt wilson group position)

open WilsonProjectiveCapture public

wilsonHasFiniteProjectionSupport :
  ∀ {G X Configuration Position}
    {structural : Structural.StructuralSourceBundle G X}
    (wilson :
      R530.StructuralWilsonLocalData
        G X Configuration Position structural)
    (projection : ProjectiveConfigurationProjection Configuration)
    (capture : WilsonProjectiveCapture G X Configuration Position structural wilson projection)
    group position →
  FiniteProjectionSupport projection
    (R529.localObservable
      (R530.asWilsonLocalObservableFamily wilson)
      group position)
wilsonHasFiniteProjectionSupport wilson projection capture group position = record
  { cutoff = cutoffFor capture group position
  ; determinedByCutoff =
      λ left right sameProjection →
        R529.wilsonObservableLocal
          (R530.R529.source
            (R530.asWilsonLocalObservableFamily wilson)
            group)
          position left right
          (projectionAgreementImpliesPathAgreement
            capture group position left right sameProjection)
  }

------------------------------------------------------------------------
-- Specialize R553's finite-cylinder predicate to finite projective support.
------------------------------------------------------------------------

record FiniteProjectionConvergenceAuthority
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (projection : ProjectiveConfigurationProjection Configuration)
    : Set₂ where
  field
    finiteSupportConvergesToProjectiveIntegral :
      ∀ observable →
      FiniteProjectionSupport projection observable →
      DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact.Converges
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        (λ cutoff → Limit.finiteExpectation family cutoff observable)
        (DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact.integrate
          (R547.extensionAuthority representation)
          (R547.representedMeasure representation)
          observable)

open FiniteProjectionConvergenceAuthority public

asProjectiveCylinderFunctionConvergenceAuthority :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family representation projection} →
  FiniteProjectionConvergenceAuthority
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation projection →
  R553.ProjectiveCylinderFunctionConvergenceAuthority
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation
asProjectiveCylinderFunctionConvergenceAuthority authority = record
  { R553.ProjectiveCylinderFunctionConvergenceAuthority.IsFiniteCylinderFunction =
      FiniteProjectionSupport _
  ; R553.ProjectiveCylinderFunctionConvergenceAuthority.finiteCylinderFunctionConvergesToProjectiveIntegral =
      finiteSupportConvergesToProjectiveIntegral authority
  }

round554WilsonFiniteSupportCompilerLevel : ProofLevel
round554WilsonFiniteSupportCompilerLevel = machineChecked

round554FiniteProjectionConvergenceAuthorityLevel : ProofLevel
round554FiniteProjectionConvergenceAuthorityLevel = standardImported

-- Genuine YM geometry seam after R529/R530:
-- the preferred projective cutoff must actually capture the finitely many edges
-- used by each selected Wilson path.
literalRound554ProjectiveCutoffCapturesWilsonPathLevel : ProofLevel
literalRound554ProjectiveCutoffCapturesWilsonPathLevel = conditional
