{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact where

------------------------------------------------------------------------
-- ROUND320 / CONSUMER-FIRST H1 SOURCE PRODUCER
--
-- R318 is the correct general adapter for an externally presented source
-- theorem: its source magnitude, root and distance may differ from the selected
-- T5 presentation, so three same-object/application equalities are required.
--
-- For proof search on the already-selected T5 carrier, however, those three
-- presentation coordinates are unnecessary.  The least-privilege producer is
-- one theorem on the exact consumer carrier:
--
--   |D^2 log Z|_selected <= selected rooted connecting shell.
--
-- Normalized two-source calculus then transports this theorem to the literal
-- selected J directions.  The root and distance are definitionally the same
-- selected root/distance, rather than being supplied by separate welds.
--
-- This module is a compiler/ABI reduction only.  It does NOT inhabit the
-- physical analytic theorem below.  R318 remains useful when importing a source
-- theorem whose coordinates are not definitionally the selected T5 ones.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318

record DirectSelectedT5MarkedDecayPayment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    -- The sole theorem-bearing physical/source field of this preferred ABI.
    -- It is stated on the normalized source calculus before literal-J
    -- presentation transport.
    mixedDerivativeMagnitudeBelowSelectedShell :
      ∀ cutoff left right →
      R278.magnitude extension
        (Cumulant.mixedSecondLogDerivative (R318.calculus base)
          left right cutoff)
      ≤ Shell.rootedShell (R318.shellData base)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right)

open DirectSelectedT5MarkedDecayPayment public

literalSelectedJMagnitudeBelowShell :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension} →
  DirectSelectedT5MarkedDecayPayment base →
  ∀ cutoff left right →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
      (Cumulant.sourceDirectionOf (R318.meaning base) left)
      (Cumulant.sourceDirectionOf (R318.meaning base) right)
      cutoff)
  ≤ Shell.rootedShell (R318.shellData base)
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff)
      (R318.connectingRoot base cutoff left right)
      (R318.physicalDistance base left right)
literalSelectedJMagnitudeBelowShell {extension = extension} {base = base}
    payment cutoff left right =
  let
    directionEquality =
      cong (λ response → response cutoff)
        (Cumulant.logSecondDirectionAgrees (R318.meaning base) left right)

    magnitudeEquality = cong (R278.magnitude extension) directionEquality

    selectedBound =
      mixedDerivativeMagnitudeBelowSelectedShell payment cutoff left right
  in
  subst
    (λ lower → lower ≤ Shell.rootedShell (R318.shellData base)
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff)
      (R318.connectingRoot base cutoff left right)
      (R318.physicalDistance base left right))
    (sym magnitudeEquality)
    selectedBound

localizeBaseDirectlyAsR295 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  DirectSelectedT5MarkedDecayPayment base →
  R295.DirectT5StateFamilyJPresentation dataSet extension
localizeBaseDirectlyAsR295 base payment = record
  { R295.DirectT5StateFamilyJPresentation.Scale = R318.Scale base
  ; R295.DirectT5StateFamilyJPresentation.Volume = R318.Volume base
  ; R295.DirectT5StateFamilyJPresentation.Root = R318.Root base
  ; R295.DirectT5StateFamilyJPresentation.SourceDirection = R318.SourceDirection base
  ; R295.DirectT5StateFamilyJPresentation.calculus = R318.calculus base
  ; R295.DirectT5StateFamilyJPresentation.meaning = R318.meaning base
  ; R295.DirectT5StateFamilyJPresentation.shellData = R318.shellData base
  ; R295.DirectT5StateFamilyJPresentation.scaleOf = R318.scaleOf base
  ; R295.DirectT5StateFamilyJPresentation.volumeOf = R318.volumeOf base
  ; R295.DirectT5StateFamilyJPresentation.physicalDistance = R318.physicalDistance base
  ; R295.DirectT5StateFamilyJPresentation.connectingRoot = R318.connectingRoot base
  ; R295.DirectT5StateFamilyJPresentation.ConnectingClusterMeetsBothSupports =
      R318.ConnectingClusterMeetsBothSupports base
  ; R295.DirectT5StateFamilyJPresentation.signedBelowMagnitude =
      R318.signedBelowMagnitude base
  ; R295.DirectT5StateFamilyJPresentation.differentiatedSourceMagnitudeBoundOnSelectedDirections =
      literalSelectedJMagnitudeBelowShell payment
  }

record Round320Boundary : Set where
  constructor round320-boundary
  field
    preferredProducerHasOneTheoremBearingField : Bool
    preferredProducerHasOneTheoremBearingFieldIsTrue :
      preferredProducerHasOneTheoremBearingField ≡ true

    separateSourceMagnitudeApplicabilityRequired : Bool
    separateSourceMagnitudeApplicabilityRequiredIsFalse :
      separateSourceMagnitudeApplicabilityRequired ≡ false

    separateSourceRootApplicabilityRequired : Bool
    separateSourceRootApplicabilityRequiredIsFalse :
      separateSourceRootApplicabilityRequired ≡ false

    separateSourceDistanceApplicabilityRequired : Bool
    separateSourceDistanceApplicabilityRequiredIsFalse :
      separateSourceDistanceApplicabilityRequired ≡ false

    normalizedSourceToLiteralJTransportIsCompiler : Bool
    normalizedSourceToLiteralJTransportIsCompilerIsTrue :
      normalizedSourceToLiteralJTransportIsCompiler ≡ true

    directSelectedDecayIsAlreadyProved : Bool
    directSelectedDecayIsAlreadyProvedIsFalse :
      directSelectedDecayIsAlreadyProved ≡ false

    generalR318ExternalAdapterStillUseful : Bool
    generalR318ExternalAdapterStillUsefulIsTrue :
      generalR318ExternalAdapterStillUseful ≡ true

canonicalRound320Boundary : Round320Boundary
canonicalRound320Boundary =
  round320-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl

round320DirectSelectedMarkedDecayLevel : ProofLevel
round320DirectSelectedMarkedDecayLevel = conditional

round320LiteralJTransportCompilerLevel : ProofLevel
round320LiteralJTransportCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
