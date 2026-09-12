{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact where

------------------------------------------------------------------------
-- ROUND296 / EXACT T5 SOURCE ALGEBRA + MAGNITUDE CORRECTION
--
-- The concurrent R295 T5 source-algebra owner removes the old post-hoc
-- covariance same-object payment at the SIGNED level:
--
--   source connected cumulant = exact finite-T5 covariance value   (refl).
--
-- The magnitude-correction R295 owner separately records the WrongType that
-- the signed cumulant is not itself the nonnegative covariance magnitude used
-- by B1.  Compose the two here.  The only source-facing localization payment is
-- now stated in the correct form
--
--   |D^2_J log Z(F,G)| <= rooted connecting shell.
--
-- Once R278's rational magnitude is identified with absolute value, the direct
-- finite-T5 covariance magnitude shell is compiler output.  Therefore R294's
-- separate source-covariance/T5 same-object coordinate is no longer physical
-- debt on this preferred presentation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as T5Source
import DASHI.Physics.YangMills.BalabanCMP116TwoJMagnitudeCorrectionRound295Exact as Magnitude295
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284

record ExactT5JMagnitudePresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    source : T5Source.DirectT5StateFamilyJPresentation dataSet extension

    -- Concrete scalar interpretation used by the canonical B1 covariance
    -- magnitude.
    t5MagnitudeIsRationalAbsolute : ∀ value →
      R278.magnitude extension value ≡ ∣ value ∣

    -- Correct physical/source theorem.  This supersedes use of the signed
    -- one-sided field as a magnitude estimate.
    literalTwoJMagnitudeBelowConnectingShell : ∀ cutoff left right →
      ∣ Cumulant.literalMixedSecondLogDerivative
          (T5Source.meaning source)
          (Cumulant.sourceDirectionOf (T5Source.meaning source) left)
          (Cumulant.sourceDirectionOf (T5Source.meaning source) right)
          cutoff ∣
      ≤ Shell.rootedShell (T5Source.shellData source)
          (T5Source.scaleOf source cutoff)
          (T5Source.volumeOf source cutoff)
          (T5Source.connectingRoot source cutoff left right)
          (T5Source.physicalDistance source left right)

open ExactT5JMagnitudePresentation public

asMagnitudeCorrectedPresentation :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  ExactT5JMagnitudePresentation dataSet extension →
  Magnitude295.CorrectedT5TwoJMagnitudePresentation dataSet extension
asMagnitudeCorrectedPresentation {dataSet = dataSet} {extension = extension}
    presentation = record
  { Magnitude295.CorrectedT5TwoJMagnitudePresentation.Scale =
      T5Source.Scale (source presentation)
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.Volume =
      T5Source.Volume (source presentation)
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.Root =
      T5Source.Root (source presentation)
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.SourceDirection =
      T5Source.SourceDirection (source presentation)
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.sourceFamily =
      T5Source.asR293StateFamily (source presentation)
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.sourceSignedCovarianceIsSelectedT5Value =
      λ cutoff left right →
        T5Source.sourceConnectedCovarianceIsExactFiniteT5
          dataSet extension left right cutoff
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.t5MagnitudeIsRationalAbsolute =
      t5MagnitudeIsRationalAbsolute presentation
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.literalTwoJMagnitudeBelowConnectingShell =
      literalTwoJMagnitudeBelowConnectingShell presentation
  ; Magnitude295.CorrectedT5TwoJMagnitudePresentation.ConnectingClusterMeetsBothSupports =
      T5Source.ConnectingClusterMeetsBothSupports (source presentation)
  }

asDirectT5TwoSourceShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  ExactT5JMagnitudePresentation dataSet extension →
  R284.DirectT5TwoSourceShell dataSet extension
asDirectT5TwoSourceShell presentation =
  Magnitude295.asCorrectedDirectT5TwoSourceShell
    (asMagnitudeCorrectedPresentation presentation)

record Round296Boundary : Set where
  constructor round296-boundary
  field
    signedSourceCovarianceT5SameObjectStillPhysical : Bool
    signedSourceCovarianceT5SameObjectStillPhysicalIsFalse :
      signedSourceCovarianceT5SameObjectStillPhysical ≡ false

    signedCumulantPromotedToMagnitudeWithoutAbs : Bool
    signedCumulantPromotedToMagnitudeWithoutAbsIsFalse :
      signedCumulantPromotedToMagnitudeWithoutAbs ≡ false

    literalAbsoluteTwoJLocalizationRequired : Bool
    literalAbsoluteTwoJLocalizationRequiredIsTrue :
      literalAbsoluteTwoJLocalizationRequired ≡ true

    correctedDirectB1ShellCompilerOwned : Bool
    correctedDirectB1ShellCompilerOwnedIsTrue :
      correctedDirectB1ShellCompilerOwned ≡ true

canonicalRound296Boundary : Round296Boundary
canonicalRound296Boundary =
  round296-boundary false refl false refl true refl true refl

round296ExactT5SourceSameObjectLevel : ProofLevel
round296ExactT5SourceSameObjectLevel =
  T5Source.round295SourceCovarianceSelectedT5SameObjectLevel

round296MagnitudeCorrectionCompilerLevel : ProofLevel
round296MagnitudeCorrectionCompilerLevel =
  Magnitude295.round295MagnitudeCorrectionCompilerLevel

round296DirectB1ShellCompilerLevel : ProofLevel
round296DirectB1ShellCompilerLevel = machineChecked

round296LiteralAbsoluteTwoJLocalizationLevel : ProofLevel
round296LiteralAbsoluteTwoJLocalizationLevel = conditional
