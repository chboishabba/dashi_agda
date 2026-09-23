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
  (ℝ; _*ℝ_; absℝ; _≤ℝ_)
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

round421PhysicalCanonicalR406CompilerLevel : ProofLevel
round421PhysicalCanonicalR406CompilerLevel = machineChecked

-- Scale, volume, root and distance are no longer separate B-shell fields.
round421IndependentPhysicalCoordinateWeldsRequired : Bool
round421IndependentPhysicalCoordinateWeldsRequired = false

-- No fresh decay theorem appears on this route.
round421AdditionalDecayTheoremRequired : Bool
round421AdditionalDecayTheoremRequired = false

-- These are the two genuine physical/source inputs left in this local package.
round421OuterSourceSummabilityLevel : ProofLevel
round421OuterSourceSummabilityLevel = conditional

round421BoundaryMixedLogSameObjectLevel : ProofLevel
round421BoundaryMixedLogSameObjectLevel = conditional
