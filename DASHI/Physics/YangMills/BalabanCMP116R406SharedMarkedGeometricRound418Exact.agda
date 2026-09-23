{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Exact where

------------------------------------------------------------------------
-- ROUND418 / SHORTEST R406 -> SHARED-MARKED GEOMETRIC DECAY
--
-- R406 already proves
--
--   |selectedBoundary| <= selectedConnectingShell
--
-- after the literal term expansion and both finite summations.
--
-- The shared marked analytic owner already proves
--
--   markedAnalyticShell(hessianMark, d)
--     <= markedBaseEnergy(hessianMark) * 2^{-d}.
--
-- Therefore the minimum Clay-facing bridge does NOT require rebuilding the
-- selected shell as an explicit per-domain R411/R414 amplitude decomposition.
-- It only needs the same-object identification
--
--   selectedConnectingShell
--     = embed(markedAnalyticShell(..., selectedDistance)).
--
-- The theorem below transports the existing rational shared-marked estimate
-- to the real R406 carrier using the existing R208 ordered ring embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; absℝ; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Add
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Ord

embedQ : R208.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  Ord.embed (Add.base (R208.additive embedding))

record R406SharedMarkedGeometricAttachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (Scale Volume Root : Set) : Set₂ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    embedding : R208.RationalRealRingEmbedding

    selectedScale : Scale
    selectedVolume : Volume
    selectedRoot : Root
    selectedDistance : Nat

    -- Sole same-object shell attachment at this layer.
    selectedConnectingShellIsSharedMarkedShell :
      R406.selectedConnectingShell application
      ≡
      embedQ embedding
        (Shared.markedAnalyticShell shared Shared.hessianMark
          selectedScale selectedVolume selectedRoot selectedDistance)

open R406SharedMarkedGeometricAttachment public

embeddedSharedMarkedShellGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application Scale Volume Root}
    (attachment :
      R406SharedMarkedGeometricAttachment
        {dataSet = dataSet} {extension = extension} {base = base}
        application Scale Volume Root) →
  embedQ (embedding attachment)
    (Shared.markedAnalyticShell
      (shared attachment) Shared.hessianMark
      (selectedScale attachment)
      (selectedVolume attachment)
      (selectedRoot attachment)
      (selectedDistance attachment))
  ≤ℝ
  embedQ (embedding attachment)
    (Geometric.markedBaseEnergy (shared attachment) Shared.hessianMark)
  *ℝ
  embedQ (embedding attachment)
    (Geo.halfPower (selectedDistance attachment))
embeddedSharedMarkedShellGeometricHalf attachment =
  let
    embedding = embedding attachment
    ordered = Add.base (R208.additive embedding)

    rationalBound =
      Geometric.markedAnalyticShellGeometricHalf
        (shared attachment) Shared.hessianMark
        (selectedScale attachment)
        (selectedVolume attachment)
        (selectedRoot attachment)
        (selectedDistance attachment)

    transported :
      embedQ embedding
        (Shared.markedAnalyticShell
          (shared attachment) Shared.hessianMark
          (selectedScale attachment)
          (selectedVolume attachment)
          (selectedRoot attachment)
          (selectedDistance attachment))
      ≤ℝ
      embedQ embedding
        (Geometric.markedBaseEnergy (shared attachment) Shared.hessianMark
          * Geo.halfPower (selectedDistance attachment))
    transported =
      Ord.orderPreserving ordered rationalBound
  in
  subst
    (λ upper →
      embedQ embedding
        (Shared.markedAnalyticShell
          (shared attachment) Shared.hessianMark
          (selectedScale attachment)
          (selectedVolume attachment)
          (selectedRoot attachment)
          (selectedDistance attachment))
      ≤ℝ upper)
    (R208.multiplyExact embedding
      (Geometric.markedBaseEnergy (shared attachment) Shared.hessianMark)
      (Geo.halfPower (selectedDistance attachment)))
    transported

selectedBoundaryBelowSharedMarkedGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application Scale Volume Root}
    (attachment :
      R406SharedMarkedGeometricAttachment
        {dataSet = dataSet} {extension = extension} {base = base}
        application Scale Volume Root) →
  absℝ (R406.selectedBoundaryIntegrand application)
  ≤ℝ
  embedQ (embedding attachment)
    (Geometric.markedBaseEnergy (shared attachment) Shared.hessianMark)
  *ℝ
  embedQ (embedding attachment)
    (Geo.halfPower (selectedDistance attachment))
selectedBoundaryBelowSharedMarkedGeometricHalf
    {application = application} attachment =
  let
    boundaryBelowSelected =
      R406.selectedBoundaryLocalizationFromR404R405 application

    boundaryBelowShared :
      absℝ (R406.selectedBoundaryIntegrand application)
      ≤ℝ
      embedQ (embedding attachment)
        (Shared.markedAnalyticShell
          (shared attachment) Shared.hessianMark
          (selectedScale attachment)
          (selectedVolume attachment)
          (selectedRoot attachment)
          (selectedDistance attachment))
    boundaryBelowShared =
      subst
        (λ upper →
          absℝ (R406.selectedBoundaryIntegrand application) ≤ℝ upper)
        (selectedConnectingShellIsSharedMarkedShell attachment)
        boundaryBelowSelected
  in
  ≤ℝ-trans
    boundaryBelowShared
    (embeddedSharedMarkedShellGeometricHalf attachment)

round418R406SharedMarkedGeometricCompilerLevel : ProofLevel
round418R406SharedMarkedGeometricCompilerLevel = machineChecked

-- The R411/R414 per-domain amplitude decomposition is useful diagnostic
-- structure, but is not mandatory for this shortest consumer once the selected
-- R406 connecting shell is identified with the already-controlled shared shell.
round418PerDomainAmplitudeDecompositionMandatory : Bool
round418PerDomainAmplitudeDecompositionMandatory = false
