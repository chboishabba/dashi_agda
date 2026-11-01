{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact where

------------------------------------------------------------------------
-- ROUND293 / STATE-FAMILY NORMALIZED SOURCE CALCULUS -> R290
--
-- R290 still stores `secondLogDerivativeIsConnectedCovariance` inside its
-- physical source presentation.  That equality is generic normalized-source
-- calculus, not Yang--Mills analysis.
--
-- Use Scalar = State -> Q.  One source calculus then represents the whole
-- finite-state/cutoff family, source directions remain state-independent, and
-- pointwise evaluation of the already checked mixed-log identity supplies the
-- R290 covariance equality at every state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact as R290

record StateFamilyTwoJSourcePresentation
    (Scale Volume Root State Observable SourceDirection : Set) : Set₁ where
  field
    algebra : Cumulant.TwoSourceMomentAlgebra Observable (State → ℚ)
    calculus : Cumulant.NormalizedLogSourceCalculus algebra
    meaning : Cumulant.LiteralTwoSourceInsertionMeaning calculus SourceDirection

    shellData : Shell.TraversalShellData Scale Volume Root
    scaleOf : State → Scale
    volumeOf : State → Volume
    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root

    -- Source-facing analytic payment only.  The left side is already the
    -- literal CMP116 mixed log-J derivative selected by `meaning`.
    differentiatedSourceBoundOnSelectedDirections : ∀ state left right →
      Cumulant.literalMixedSecondLogDerivative meaning
        (Cumulant.sourceDirectionOf meaning left)
        (Cumulant.sourceDirectionOf meaning right) state
      ≤ Shell.rootedShell shellData
          (scaleOf state) (volumeOf state)
          (connectingRoot state left right)
          (physicalDistance left right)

open StateFamilyTwoJSourcePresentation public

pointwiseMixedLogDerivativeIsConnectedCovariance :
  ∀ {Scale Volume Root State Observable SourceDirection}
    (presentation : StateFamilyTwoJSourcePresentation
      Scale Volume Root State Observable SourceDirection)
    state left right →
  Cumulant.literalMixedSecondLogDerivative (meaning presentation)
    (Cumulant.sourceDirectionOf (meaning presentation) left)
    (Cumulant.sourceDirectionOf (meaning presentation) right) state
  ≡ Cumulant.connectedCovariance (algebra presentation) left right state
pointwiseMixedLogDerivativeIsConnectedCovariance presentation state left right =
  cong (λ response → response state)
    (Cumulant.literalMixedLogDerivativeIsConnectedCovariance
      (meaning presentation) left right)

asRound290Presentation :
  ∀ {Scale Volume Root State Observable SourceDirection} →
  StateFamilyTwoJSourcePresentation
    Scale Volume Root State Observable SourceDirection →
  R290.TwoPhysicalJInsertionSourcePresentation
    Scale Volume Root State Observable SourceDirection
asRound290Presentation presentation = record
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
      λ state leftDirection rightDirection →
        Cumulant.literalMixedSecondLogDerivative (meaning presentation)
          leftDirection rightDirection state
  ; R290.TwoPhysicalJInsertionSourcePresentation.connectedCovarianceMagnitude =
      λ state left right →
        Cumulant.connectedCovariance (algebra presentation) left right state
  ; R290.TwoPhysicalJInsertionSourcePresentation.secondLogDerivativeIsConnectedCovariance =
      pointwiseMixedLogDerivativeIsConnectedCovariance presentation
  ; R290.TwoPhysicalJInsertionSourcePresentation.differentiatedSourceBoundOnSelectedDirections =
      differentiatedSourceBoundOnSelectedDirections presentation
  }

round293NormalizedSourceStateFamilyCompilerLevel : ProofLevel
round293NormalizedSourceStateFamilyCompilerLevel = machineChecked

round293SecondLogDerivativeCovarianceMeaningLevel : ProofLevel
round293SecondLogDerivativeCovarianceMeaningLevel = machineChecked

round293CMP116FiniteDerivativeLocalizationLevel : ProofLevel
round293CMP116FiniteDerivativeLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

-- Remaining source/physical seam: instantiate `meaning.sourceDirectionOf` by the
-- literal physical CMP116/CMP119 J coordinates and apply the published finite-
-- derivative localization theorem to exactly those selected directions/supports.
round293LiteralPhysicalJDirectionLocalizationLevel : ProofLevel
round293LiteralPhysicalJDirectionLocalizationLevel = conditional
