{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact where

------------------------------------------------------------------------
-- ROUND295 / SOURCE CALCULUS ON THE EXACT FINITE T5 EXPECTATION ALGEBRA
--
-- R291/R294 still carry a same-object payment saying the covariance produced by
-- the source/J presentation is the selected finite T5 covariance.  Avoid that
-- post-hoc weld entirely: instantiate the normalized source calculus on the T5
-- finite expectation algebra itself.
--
-- Scalar = cutoff -> Q
-- expectation(F)(n) = E_{mu_n}[F]
-- productObservable   = the exact T5 observable product
-- multiplication      = the exact T5 scalar multiplication pointwise
-- subtraction         = x + (-y) using the exact R278 extension
--
-- Then `Cumulant.connectedCovariance` is definitionally the R278 connected
-- covariance value at every cutoff.  The only remaining physical source work is
-- to supply the literal CMP116/CMP119 source calculus/J-direction semantics and
-- its differentiated rooted-shell bound on this SAME expectation carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanDirectT5JInsertionShellAdapterRound291Exact as R291
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact as R290

------------------------------------------------------------------------
-- Exact T5 finite expectation algebra as a state-family source algebra.
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
-- Physical source presentation, but now based on the exact T5 algebra.
------------------------------------------------------------------------

record T5LiteralTwoJSourcePresentation
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root SourceDirection : Set

    calculus : Cumulant.NormalizedLogSourceCalculus
      (t5FiniteExpectationAlgebra dataSet extension)

    meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection

    stateFamily :
      R293.StateFamilyTwoJSourcePresentation
        Scale Volume Root Nat TestObservable SourceDirection

    -- The state-family source calculus must be this exact T5 calculus/meaning,
    -- not an independently named isomorphic source object.
    stateFamilyCalculusIsT5 : R293.calculus stateFamily ≡ calculus
    stateFamilyMeaningIsT5 :
      R293.meaning stateFamily ≡
        substMeaning stateFamilyCalculusIsT5 meaning

open T5LiteralTwoJSourcePresentation public

-- Transport a literal source-direction meaning along equality of calculus.
substMeaning :
  ∀ {Observable Scalar SourceDirection}
    {algebra : Cumulant.TwoSourceMomentAlgebra Observable Scalar}
    {first second : Cumulant.NormalizedLogSourceCalculus algebra} →
  first ≡ second →
  Cumulant.LiteralTwoSourceInsertionMeaning second SourceDirection →
  Cumulant.LiteralTwoSourceInsertionMeaning first SourceDirection
substMeaning refl meaning = meaning

------------------------------------------------------------------------
-- A lower-friction canonical presentation: require the R293 state family to be
-- constructed directly from the exact T5 algebra, so covariance equality is
-- definitional and R291's old same-object field is compiler output.
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

    shellData :
      R290.Shell.TraversalShellData Scale Volume Root
    scaleOf : Nat → Scale
    volumeOf : Nat → Volume
    physicalDistance : TestObservable → TestObservable → Nat
    connectingRoot : Nat → TestObservable → TestObservable → Root

    differentiatedSourceBoundOnSelectedDirections : ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative meaning
        (Cumulant.sourceDirectionOf meaning left)
        (Cumulant.sourceDirectionOf meaning right) cutoff
      R290.Shell._≤_
        R290.Shell.rootedShell shellData
          (scaleOf cutoff) (volumeOf cutoff)
          (connectingRoot cutoff left right)
          (physicalDistance left right)

open DirectT5StateFamilyJPresentation public

asR293StateFamily :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (presentation : DirectT5StateFamilyJPresentation dataSet extension) →
  R293.StateFamilyTwoJSourcePresentation
    (Scale presentation) (Volume presentation) (Root presentation)
    Nat TestObservable (SourceDirection presentation)
asR293StateFamily {dataSet = dataSet} {extension = extension} presentation = record
  { R293.StateFamilyTwoJSourcePresentation.algebra =
      t5FiniteExpectationAlgebra dataSet extension
  ; R293.StateFamilyTwoJSourcePresentation.calculus = calculus presentation
  ; R293.StateFamilyTwoJSourcePresentation.meaning = meaning presentation
  ; R293.StateFamilyTwoJSourcePresentation.shellData = shellData presentation
  ; R293.StateFamilyTwoJSourcePresentation.scaleOf = scaleOf presentation
  ; R293.StateFamilyTwoJSourcePresentation.volumeOf = volumeOf presentation
  ; R293.StateFamilyTwoJSourcePresentation.physicalDistance = physicalDistance presentation
  ; R293.StateFamilyTwoJSourcePresentation.connectingRoot = connectingRoot presentation
  ; R293.StateFamilyTwoJSourcePresentation.differentiatedSourceBoundOnSelectedDirections =
      differentiatedSourceBoundOnSelectedDirections presentation
  }

asR291Presentation :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (presentation : DirectT5StateFamilyJPresentation dataSet extension) →
  R291.DirectT5JInsertionShellPresentation dataSet extension
asR291Presentation {dataSet = dataSet} {extension = extension} presentation = record
  { R291.DirectT5JInsertionShellPresentation.Scale = Scale presentation
  ; R291.DirectT5JInsertionShellPresentation.Volume = Volume presentation
  ; R291.DirectT5JInsertionShellPresentation.Root = Root presentation
  ; R291.DirectT5JInsertionShellPresentation.SourceDirection = SourceDirection presentation
  ; R291.DirectT5JInsertionShellPresentation.sourcePresentation =
      R293.asRound290Presentation (asR293StateFamily presentation)
  ; R291.DirectT5JInsertionShellPresentation.sourceCovarianceIsSelectedT5Covariance =
      λ cutoff left right → refl
  ; R291.DirectT5JInsertionShellPresentation.ConnectingClusterMeetsBothSupports =
      λ _ _ _ → Set
  }

round295ExactT5SourceAlgebraCompilerLevel : ProofLevel
round295ExactT5SourceAlgebraCompilerLevel = machineChecked

round295SourceCovarianceSelectedT5SameObjectLevel : ProofLevel
round295SourceCovarianceSelectedT5SameObjectLevel = machineChecked

-- Single remaining D1 physical/source seam on this canonical presentation:
-- instantiate the actual CMP116/CMP119 normalized source calculus/J directions
-- and the published differentiated rooted-shell estimate on the exact T5 finite
-- expectation carrier.
round295LiteralT5JDirectionLocalizationLevel : ProofLevel
round295LiteralT5JDirectionLocalizationLevel = conditional
