{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalCanonicalR406Round421Exact where

------------------------------------------------------------------------
-- ROUND421 / LITERAL PHYSICAL R318 COORDINATES FOR THE SHORTEST R406 B ROUTE
--
-- R419 canonicalized the terminal R406 shell but still allowed arbitrary
-- scale/volume/root/distance coordinates.  The minimum Clay route needs only
-- the literal selected physical coordinates already carried by R318:
--
--   scaleOf cutoff,
--   volumeOf cutoff,
--   connectingRoot cutoff left right,
--   physicalDistance left right.
--
-- This owner chooses those coordinates definitionally.  Hence there is no
-- separate B-shell root/distance/scale/volume identification theorem.
--
-- Remaining source payments on this shortest lane:
--
--   (1) the R406 outer common-Y sum is below the shared hessian shell at those
--       literal physical coordinates;
--   (2) the canonical R406 selected boundary magnitude is the literal mixed-J
--       response magnitude.
--
-- R420 + R341 then compile directly to the finite selected covariance bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Exact as R418
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSharedShellR406Round419Exact as R419
import DASHI.Physics.YangMills.BalabanCMP116CanonicalR406MixedLogRound420Exact as R420
import DASHI.Physics.YangMills.BalabanCMP116ExternalMarkResidualSummationRound423Exact as R423

record PhysicalCanonicalR406Inputs
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (cutoff : Nat)
    (left right : TestObservable) : Set₂ where
  field
    shared :
      Shared.SharedMarkedAnalyticShellControl
        (R318.Scale base) (R318.Volume base) (R318.Root base)

    embedding : R208.RationalRealRingEmbedding

    commonYShellsBelowPhysicalSharedMarkedShell :
      Resum.sumℝ
        (R406.commonYShell application)
        (R406.localizedDomains application)
      ≤ℝ
      R418.embedQ embedding
        (Shared.markedAnalyticShell shared Shared.hessianMark
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right))

    selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude :
      absℝ
        (R406.selectedBoundaryIntegrand application)
      ≡
      R418.embedQ embedding
        (R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative
            (R318.meaning base)
            (Cumulant.sourceDirectionOf (R318.meaning base) left)
            (Cumulant.sourceDirectionOf (R318.meaning base) right)
            cutoff))

open PhysicalCanonicalR406Inputs public

------------------------------------------------------------------------
-- Source-faithful factorization of the outer R406 payment.
--
-- Do not ask the physical producer for the already-summed inequality if CMP116
-- supplies the stronger mechanism:
--
--   commonYShell(Y) <= externalMarkedWeight * residualWeight(Y)
--   sum residualWeight <= residualEnvelope.
--
-- R423 proves the finite positive summation.  The only extra same-object
-- coordinate here identifies the factored envelope with the literal shared
-- hessian shell selected above.
------------------------------------------------------------------------

record PhysicalFactoredR406Inputs
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (cutoff : Nat)
    (left right : TestObservable) : Set₂ where
  field
    shared :
      Shared.SharedMarkedAnalyticShellControl
        (R318.Scale base) (R318.Volume base) (R318.Root base)

    embedding : R208.RationalRealRingEmbedding

    residualWeight : R406.Domain application → ℝ
    externalMarkedWeight residualEnvelope : ℝ

    externalMarkedWeightNonnegative :
      0ℝ ≤ℝ externalMarkedWeight

    residualWeightNonnegative :
      ∀ domain →
      0ℝ ≤ℝ residualWeight domain

    commonYShellBelowExternalTimesResidual :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ externalMarkedWeight *ℝ residualWeight domain

    residualSummability :
      Resum.sumℝ residualWeight (R406.localizedDomains application)
      ≤ℝ residualEnvelope

    factoredEnvelopeIsPhysicalSharedMarkedShell :
      externalMarkedWeight *ℝ residualEnvelope
      ≡
      R418.embedQ embedding
        (Shared.markedAnalyticShell shared Shared.hessianMark
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right))

    selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude :
      absℝ
        (R406.selectedBoundaryIntegrand application)
      ≡
      R418.embedQ embedding
        (R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative
            (R318.meaning base)
            (Cumulant.sourceDirectionOf (R318.meaning base) left)
            (Cumulant.sourceDirectionOf (R318.meaning base) right)
            cutoff))

open PhysicalFactoredR406Inputs public

asExternalMarkedResidualSummationData :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right} →
  PhysicalFactoredR406Inputs
    {dataSet = dataSet} {extension = extension} {base = base}
    application cutoff left right →
  R423.ExternalMarkedResidualSummationData (R406.Domain application)
asExternalMarkedResidualSummationData
    {application = application} inputs = record
  { R423.ExternalMarkedResidualSummationData.domains =
      R406.localizedDomains application
  ; R423.ExternalMarkedResidualSummationData.commonYShell =
      R406.commonYShell application
  ; R423.ExternalMarkedResidualSummationData.residualWeight =
      residualWeight inputs
  ; R423.ExternalMarkedResidualSummationData.externalMarkedWeight =
      externalMarkedWeight inputs
  ; R423.ExternalMarkedResidualSummationData.residualEnvelope =
      residualEnvelope inputs
  ; R423.ExternalMarkedResidualSummationData.externalMarkedWeightNonnegative =
      externalMarkedWeightNonnegative inputs
  ; R423.ExternalMarkedResidualSummationData.residualWeightNonnegative =
      residualWeightNonnegative inputs
  ; R423.ExternalMarkedResidualSummationData.commonYShellBelowExternalTimesResidual =
      commonYShellBelowExternalTimesResidual inputs
  ; R423.ExternalMarkedResidualSummationData.residualSummability =
      residualSummability inputs
  }

asPhysicalCanonicalR406InputsFromFactored :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right}
    (inputs :
      PhysicalFactoredR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application cutoff left right) →
  PhysicalCanonicalR406Inputs
    {dataSet = dataSet} {extension = extension} {base = base}
    application cutoff left right
asPhysicalCanonicalR406InputsFromFactored
    {base = base} {application = application}
    {cutoff = cutoff} {left = left} {right = right}
    inputs = record
  { PhysicalCanonicalR406Inputs.shared =
      shared inputs
  ; PhysicalCanonicalR406Inputs.embedding =
      embedding inputs
  ; PhysicalCanonicalR406Inputs.commonYShellsBelowPhysicalSharedMarkedShell =
      R423.sumCommonYShellBelowTarget
        (asExternalMarkedResidualSummationData inputs)
        (R418.embedQ (embedding inputs)
          (Shared.markedAnalyticShell (shared inputs) Shared.hessianMark
            (R318.scaleOf base cutoff)
            (R318.volumeOf base cutoff)
            (R318.connectingRoot base cutoff left right)
            (R318.physicalDistance base left right)))
        (factoredEnvelopeIsPhysicalSharedMarkedShell inputs)
  ; PhysicalCanonicalR406Inputs.selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude =
      selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude inputs
  }


asCanonicalSharedShellInputs :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right} →
  PhysicalCanonicalR406Inputs
    {dataSet = dataSet} {extension = extension} {base = base}
    application cutoff left right →
  R419.CanonicalSharedShellR406Inputs
    {dataSet = dataSet} {extension = extension} {base = base}
    application
    (R318.Scale base) (R318.Volume base) (R318.Root base)
asCanonicalSharedShellInputs
    {base = base} {cutoff = cutoff} {left = left} {right = right}
    inputs = record
  { R419.CanonicalSharedShellR406Inputs.shared =
      shared inputs
  ; R419.CanonicalSharedShellR406Inputs.embedding =
      embedding inputs
  ; R419.CanonicalSharedShellR406Inputs.selectedScale =
      R318.scaleOf base cutoff
  ; R419.CanonicalSharedShellR406Inputs.selectedVolume =
      R318.volumeOf base cutoff
  ; R419.CanonicalSharedShellR406Inputs.selectedRoot =
      R318.connectingRoot base cutoff left right
  ; R419.CanonicalSharedShellR406Inputs.selectedDistance =
      R318.physicalDistance base left right
  ; R419.CanonicalSharedShellR406Inputs.commonYShellsBelowSharedMarkedShell =
      commonYShellsBelowPhysicalSharedMarkedShell inputs
  }

asCanonicalMixedLogAttachment :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right}
    (inputs :
      PhysicalCanonicalR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application cutoff left right) →
  R420.CanonicalR406MixedLogAttachment
    (asCanonicalSharedShellInputs inputs) cutoff left right
asCanonicalMixedLogAttachment
    {application = application} inputs = record
  { R420.CanonicalR406MixedLogAttachment.selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude =
      selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude inputs
  }

physicalFiniteSelectedCovarianceBelowSharedMarkedGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right}
    (inputs :
      PhysicalCanonicalR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application cutoff left right) →
  R418.embedQ (embedding inputs)
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      left right)
  ≤ℝ
  R418.embedQ (embedding inputs)
    (Geometric.markedBaseEnergy (shared inputs) Shared.hessianMark)
  *ℝ
  R418.embedQ (embedding inputs)
    (Geo.halfPower (R318.physicalDistance base left right))
physicalFiniteSelectedCovarianceBelowSharedMarkedGeometricHalf inputs =
  R420.finiteSelectedCovarianceMagnitudeBelowSharedMarkedGeometricHalf
    (asCanonicalMixedLogAttachment inputs)

physicalFiniteSelectedCovarianceFromFactoredSource :
  ∀ {Measure TestObservable dataSet extension base application cutoff left right}
    (inputs :
      PhysicalFactoredR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application cutoff left right) →
  R418.embedQ (embedding inputs)
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      left right)
  ≤ℝ
  R418.embedQ (embedding inputs)
    (Geometric.markedBaseEnergy (shared inputs) Shared.hessianMark)
  *ℝ
  R418.embedQ (embedding inputs)
    (Geo.halfPower (R318.physicalDistance base left right))
physicalFiniteSelectedCovarianceFromFactoredSource inputs =
  physicalFiniteSelectedCovarianceBelowSharedMarkedGeometricHalf
    (asPhysicalCanonicalR406InputsFromFactored inputs)

round421PhysicalCanonicalR406CompilerLevel : ProofLevel
round421PhysicalCanonicalR406CompilerLevel = machineChecked

-- Scale, volume, root and distance are no longer separate B-shell fields.
round421IndependentPhysicalCoordinateWeldsRequired : Bool
round421IndependentPhysicalCoordinateWeldsRequired = false

-- No fresh decay theorem appears on this route.
round421AdditionalDecayTheoremRequired : Bool
round421AdditionalDecayTheoremRequired = false

-- R423 removes the already-summed outer inequality as a primitive input on the
-- factored source route.  The genuinely live analytic/source leaves are now the
-- pointwise marked/residual factorization and residual CMP116 summability.
round421OuterSourceSummabilityLevel : ProofLevel
round421OuterSourceSummabilityLevel = machineChecked

round421PointwiseMarkedResidualFactorizationLevel : ProofLevel
round421PointwiseMarkedResidualFactorizationLevel = conditional

round421ResidualCMP116SummabilityLevel : ProofLevel
round421ResidualCMP116SummabilityLevel = conditional

round421SharedShellFactorizationLevel : ProofLevel
round421SharedShellFactorizationLevel = conditional

round421BoundaryMixedLogSameObjectLevel : ProofLevel
round421BoundaryMixedLogSameObjectLevel = conditional
