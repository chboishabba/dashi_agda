{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact where

------------------------------------------------------------------------
-- ROUND295 / SOURCE CALCULUS ON THE EXACT FINITE T5 EXPECTATION ALGEBRA
--
-- Instantiate normalized source calculus on the exact finite T5 expectation
-- algebra, rather than constructing a second covariance carrier and welding it
-- afterwards.
--
-- Scalar = cutoff -> Q
-- expectation(F)(n) = E_{mu_n}[F]
-- productObservable   = exact T5 observable product
-- multiplication      = exact T5 scalar multiplication pointwise
-- subtraction         = x + (-y) using the exact R278 extension
--
-- The generic mixed-log identity first gives the signed connected covariance.
-- Applying the SAME R278 magnitude map then gives the exact finite T5 covariance
-- magnitude consumed by R291/R284.  No positivity/sign identification is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact as R290
import DASHI.Physics.YangMills.BalabanDirectT5JInsertionShellAdapterRound291Exact as R291
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

------------------------------------------------------------------------
-- Exact T5 finite expectation algebra as the source moment algebra.
------------------------------------------------------------------------

t5FiniteExpectationAlgebra :
  ∀ {Measure Observable}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet) →
  Cumulant.TwoSourceMomentAlgebra Observable (Nat → ℚ)
t5FiniteExpectationAlgebra dataSet extension = record
  { Cumulant.TwoSourceMomentAlgebra.subtract =
      λ first second cutoff →
        Gram.add (Gram.operations dataSet)
          (first cutoff) (R278.negate extension (second cutoff))
  ; Cumulant.TwoSourceMomentAlgebra.multiply =
      λ first second cutoff →
        Gram.multiply (Gram.operations dataSet) (first cutoff) (second cutoff)
  ; Cumulant.TwoSourceMomentAlgebra.productObservable =
      Gram.multiplyObservable (Gram.operations dataSet)
  ; Cumulant.TwoSourceMomentAlgebra.expectation =
      λ observable cutoff →
        Gram.expectation (Gram.operations dataSet)
          (Gram.measureSequence dataSet cutoff) observable
  }

sourceConnectedCovarianceIsExactFiniteT5 :
  ∀ {Measure Observable}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    left right cutoff →
  Cumulant.connectedCovariance
      (t5FiniteExpectationAlgebra dataSet extension) left right cutoff
  ≡ R278.connectedCovarianceValue extension
      (Gram.measureSequence dataSet cutoff) left right
sourceConnectedCovarianceIsExactFiniteT5 dataSet extension left right cutoff = refl

------------------------------------------------------------------------
-- Canonical direct physical presentation.
------------------------------------------------------------------------

record DirectT5StateFamilyJPresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root SourceDirection : Set

    calculus : Cumulant.NormalizedLogSourceCalculus
      (t5FiniteExpectationAlgebra dataSet extension)
    meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection

    shellData : Shell.TraversalShellData Scale Volume Root
    scaleOf : Nat → Scale
    volumeOf : Nat → Volume
    physicalDistance : TestObservable → TestObservable → Nat
    connectingRoot : Nat → TestObservable → TestObservable → Root

    ConnectingClusterMeetsBothSupports :
      Nat → TestObservable → TestObservable → Set

    -- Single source-facing analytic payment: the MAGNITUDE of the literal mixed
    -- log-J response obeys the imported CMP116 rooted-shell localization on the
    -- exact T5 finite expectation carrier.
    differentiatedSourceMagnitudeBoundOnSelectedDirections :
      ∀ cutoff left right →
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative meaning
          (Cumulant.sourceDirectionOf meaning left)
          (Cumulant.sourceDirectionOf meaning right) cutoff)
      ≤ Shell.rootedShell shellData
          (scaleOf cutoff) (volumeOf cutoff)
          (connectingRoot cutoff left right)
          (physicalDistance left right)

open DirectT5StateFamilyJPresentation public

mixedLogMagnitudeIsExactFiniteT5CovarianceMagnitude :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : DirectT5StateFamilyJPresentation dataSet extension)
    cutoff left right →
  R278.magnitude extension
    (Cumulant.literalMixedSecondLogDerivative (meaning presentation)
      (Cumulant.sourceDirectionOf (meaning presentation) left)
      (Cumulant.sourceDirectionOf (meaning presentation) right) cutoff)
  ≡ R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff) left right
mixedLogMagnitudeIsExactFiniteT5CovarianceMagnitude
    {extension = extension} presentation cutoff left right =
  cong (R278.magnitude extension)
    (cong (λ response → response cutoff)
      (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
        (meaning presentation) left right))

asR290Presentation :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (presentation : DirectT5StateFamilyJPresentation dataSet extension) →
  R290.TwoPhysicalJInsertionSourcePresentation
    (Scale presentation) (Volume presentation) (Root presentation)
    Nat TestObservable (SourceDirection presentation)
asR290Presentation {extension = extension} presentation = record
  { R290.TwoPhysicalJInsertionSourcePresentation.shellData = shellData presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.scaleOf = scaleOf presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.volumeOf = volumeOf presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.physicalDistance =
      physicalDistance presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.connectingRoot =
      connectingRoot presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.sourceDirection =
      Cumulant.sourceDirectionOf (meaning presentation)
  ; R290.TwoPhysicalJInsertionSourcePresentation.secondLogSourceDerivativeMagnitude =
      λ cutoff leftDirection rightDirection →
        R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative (meaning presentation)
            leftDirection rightDirection cutoff)
  ; R290.TwoPhysicalJInsertionSourcePresentation.connectedCovarianceMagnitude =
      λ cutoff left right →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence _) left right
  ; R290.TwoPhysicalJInsertionSourcePresentation.secondLogDerivativeIsConnectedCovariance =
      mixedLogMagnitudeIsExactFiniteT5CovarianceMagnitude presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.differentiatedSourceBoundOnSelectedDirections =
      differentiatedSourceMagnitudeBoundOnSelectedDirections presentation
  }

asR291Presentation :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (presentation : DirectT5StateFamilyJPresentation dataSet extension) →
  R291.DirectT5JInsertionShellPresentation dataSet extension
asR291Presentation presentation = record
  { R291.DirectT5JInsertionShellPresentation.Scale = Scale presentation
  ; R291.DirectT5JInsertionShellPresentation.Volume = Volume presentation
  ; R291.DirectT5JInsertionShellPresentation.Root = Root presentation
  ; R291.DirectT5JInsertionShellPresentation.SourceDirection = SourceDirection presentation
  ; R291.DirectT5JInsertionShellPresentation.sourcePresentation =
      asR290Presentation presentation
  ; R291.DirectT5JInsertionShellPresentation.sourceCovarianceIsSelectedT5Covariance =
      λ cutoff left right → refl
  ; R291.DirectT5JInsertionShellPresentation.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports presentation
  }

round295ExactT5SourceAlgebraCompilerLevel : ProofLevel
round295ExactT5SourceAlgebraCompilerLevel = machineChecked

round295LogCovarianceMagnitudeCompilerLevel : ProofLevel
round295LogCovarianceMagnitudeCompilerLevel = machineChecked

round295SourceCovarianceSelectedT5SameObjectLevel : ProofLevel
round295SourceCovarianceSelectedT5SameObjectLevel = machineChecked

-- Single remaining D1 physical/source seam on this canonical presentation:
-- instantiate the actual CMP116/CMP119 normalized source calculus/J directions
-- and the published differentiated rooted-shell MAGNITUDE estimate on the exact
-- T5 finite expectation carrier.
round295LiteralT5JDirectionLocalizationLevel : ProofLevel
round295LiteralT5JDirectionLocalizationLevel = conditional
