{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoJMagnitudeCorrectionRound295Exact where

------------------------------------------------------------------------
-- ROUND295 / WRONGTYPE REPAIR: SIGNED CUMULANT /= MAGNITUDE
--
-- R290 historically named its mixed second log-source derivative and connected
-- covariance fields `...Magnitude`, while the R293 state-family compiler fills
-- them with the SIGNED cumulant
--
--   E[FG] - E[F]E[G].
--
-- That signed identity is correct, but a one-sided estimate on it does not by
-- itself give the nonnegative covariance magnitude consumed by canonical B1.
-- This owner repairs the type boundary without rewriting the historical files:
--
--   signed literal D^2_J log Z
--     = signed connected covariance               (R293 compiler)
--     = exact selected finite-T5 covariance value (same-object receipt)
--
-- and separately
--
--   | literal D^2_J log Z | <= rooted connecting shell.
--
-- Once the T5 magnitude operation is identified with rational absolute value,
-- the exact R278 covariance magnitude is below the same shell.  Thus the direct
-- R284 B1 producer can consume a genuinely nonnegative magnitude carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact as Source293
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284

record CorrectedT5TwoJMagnitudePresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root SourceDirection : Set

    sourceFamily :
      Source293.StateFamilyTwoJSourcePresentation
        Scale Volume Root Nat TestObservable SourceDirection

    -- SAME signed covariance object: the source-family cumulant is the exact
    -- selected finite-T5 covariance value before magnitude is taken.
    sourceSignedCovarianceIsSelectedT5Value : ∀ cutoff left right →
      Cumulant.connectedCovariance (Source293.algebra sourceFamily)
        left right cutoff
      ≡ R278.connectedCovarianceValue extension
          (Gram.measureSequence dataSet cutoff) left right

    -- The concrete rational realization of R278's magnitude operator.
    t5MagnitudeIsRationalAbsolute : ∀ value →
      R278.magnitude extension value ≡ ∣ value ∣

    -- Physical/source theorem in the correct magnitude form.
    literalTwoJMagnitudeBelowConnectingShell : ∀ cutoff left right →
      ∣ Cumulant.literalMixedSecondLogDerivative
          (Source293.meaning sourceFamily)
          (Cumulant.sourceDirectionOf (Source293.meaning sourceFamily) left)
          (Cumulant.sourceDirectionOf (Source293.meaning sourceFamily) right)
          cutoff ∣
      ≤ Shell.rootedShell (Source293.shellData sourceFamily)
          (Source293.scaleOf sourceFamily cutoff)
          (Source293.volumeOf sourceFamily cutoff)
          (Source293.connectingRoot sourceFamily cutoff left right)
          (Source293.physicalDistance sourceFamily left right)

    ConnectingClusterMeetsBothSupports :
      Nat → TestObservable → TestObservable → Set

open CorrectedT5TwoJMagnitudePresentation public

selectedT5CovarianceMagnitudeBelowRootedShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : CorrectedT5TwoJMagnitudePresentation dataSet extension)
    cutoff left right →
  R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff) left right
  ≤ Shell.rootedShell (Source293.shellData (sourceFamily presentation))
      (Source293.scaleOf (sourceFamily presentation) cutoff)
      (Source293.volumeOf (sourceFamily presentation) cutoff)
      (Source293.connectingRoot (sourceFamily presentation) cutoff left right)
      (Source293.physicalDistance (sourceFamily presentation) left right)
selectedT5CovarianceMagnitudeBelowRootedShell
    {dataSet = dataSet} {extension = extension}
    presentation cutoff left right
  rewrite t5MagnitudeIsRationalAbsolute presentation
      (R278.connectedCovarianceValue extension
        (Gram.measureSequence dataSet cutoff) left right)
        | sym (sourceSignedCovarianceIsSelectedT5Value
            presentation cutoff left right)
        | sym (Source293.pointwiseMixedLogDerivativeIsConnectedCovariance
            (sourceFamily presentation) cutoff left right) =
  literalTwoJMagnitudeBelowConnectingShell presentation cutoff left right

asCorrectedDirectT5TwoSourceShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  CorrectedT5TwoJMagnitudePresentation dataSet extension →
  R284.DirectT5TwoSourceShell dataSet extension
asCorrectedDirectT5TwoSourceShell presentation = record
  { R284.DirectT5TwoSourceShell.Scale = Scale presentation
  ; R284.DirectT5TwoSourceShell.Volume = Volume presentation
  ; R284.DirectT5TwoSourceShell.Root = Root presentation
  ; R284.DirectT5TwoSourceShell.shellData =
      Source293.shellData (sourceFamily presentation)
  ; R284.DirectT5TwoSourceShell.scaleAtCutoff =
      Source293.scaleOf (sourceFamily presentation)
  ; R284.DirectT5TwoSourceShell.volumeAtCutoff =
      Source293.volumeOf (sourceFamily presentation)
  ; R284.DirectT5TwoSourceShell.physicalDistance =
      Source293.physicalDistance (sourceFamily presentation)
  ; R284.DirectT5TwoSourceShell.connectingRoot =
      Source293.connectingRoot (sourceFamily presentation)
  ; R284.DirectT5TwoSourceShell.finiteCovarianceBelowConnectingShell =
      selectedT5CovarianceMagnitudeBelowRootedShell presentation
  ; R284.DirectT5TwoSourceShell.connectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports presentation
  }

record Round295Boundary : Set where
  constructor round295-boundary
  field
    signedCumulantIsMagnitude : Bool
    signedCumulantIsMagnitudeIsFalse : signedCumulantIsMagnitude ≡ false

    absoluteValueBoundaryRequired : Bool
    absoluteValueBoundaryRequiredIsTrue : absoluteValueBoundaryRequired ≡ true

    signedLogDerivativeCovarianceIdentityCompilerOwned : Bool
    signedLogDerivativeCovarianceIdentityCompilerOwnedIsTrue :
      signedLogDerivativeCovarianceIdentityCompilerOwned ≡ true

    correctedMagnitudeToDirectB1CompilerOwned : Bool
    correctedMagnitudeToDirectB1CompilerOwnedIsTrue :
      correctedMagnitudeToDirectB1CompilerOwned ≡ true

canonicalRound295Boundary : Round295Boundary
canonicalRound295Boundary =
  round295-boundary false refl true refl true refl true refl

round295SignedCumulantCompilerLevel : ProofLevel
round295SignedCumulantCompilerLevel =
  Source293.round293SecondLogDerivativeCovarianceMeaningLevel

round295MagnitudeCorrectionCompilerLevel : ProofLevel
round295MagnitudeCorrectionCompilerLevel = machineChecked

-- Remaining physical/source theorem is now correctly stated with absolute value.
round295LiteralTwoJMagnitudeLocalizationLevel : ProofLevel
round295LiteralTwoJMagnitudeLocalizationLevel = conditional
