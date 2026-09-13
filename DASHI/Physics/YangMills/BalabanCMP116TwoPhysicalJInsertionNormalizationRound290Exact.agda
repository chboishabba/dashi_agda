{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound290Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

record TwoPhysicalJInsertionSourcePresentation
    (Scale Volume Root State Observable SourceDirection : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root
    scaleOf : State → Scale
    volumeOf : State → Volume
    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root
    sourceDirection : Observable → SourceDirection
    secondLogSourceDerivativeMagnitude :
      State → SourceDirection → SourceDirection → ℚ
    connectedCovarianceMagnitude : State → Observable → Observable → ℚ
    secondLogDerivativeIsConnectedCovariance : ∀ state left right →
      secondLogSourceDerivativeMagnitude state
        (sourceDirection left) (sourceDirection right)
      ≡ connectedCovarianceMagnitude state left right
    differentiatedSourceBoundOnSelectedDirections : ∀ state left right →
      secondLogSourceDerivativeMagnitude state
        (sourceDirection left) (sourceDirection right)
      ≤ Shell.rootedShell shellData
          (scaleOf state) (volumeOf state)
          (connectingRoot state left right)
          (physicalDistance left right)

open TwoPhysicalJInsertionSourcePresentation public

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

physicalCovarianceBelowRootedShell :
  ∀ {Scale Volume Root State Observable SourceDirection}
    (presentation : TwoPhysicalJInsertionSourcePresentation
      Scale Volume Root State Observable SourceDirection)
    state left right →
  connectedCovarianceMagnitude presentation state left right
  ≤ Shell.rootedShell (shellData presentation)
      (scaleOf presentation state) (volumeOf presentation state)
      (connectingRoot presentation state left right)
      (physicalDistance presentation left right)
physicalCovarianceBelowRootedShell presentation state left right
  rewrite symEq
    (secondLogDerivativeIsConnectedCovariance presentation state left right) =
  differentiatedSourceBoundOnSelectedDirections presentation state left right

record Round290Boundary : Set where
  constructor round290-boundary
  field
    freshTwoSourceDecayTheoremRequired : Bool
    freshTwoSourceDecayTheoremRequiredIsFalse :
      freshTwoSourceDecayTheoremRequired ≡ false
    physicalObservableToJDirectionMeaningRequired : Bool
    physicalObservableToJDirectionMeaningRequiredIsTrue :
      physicalObservableToJDirectionMeaningRequired ≡ true
    secondLogDerivativeCovarianceMeaningRequired : Bool
    secondLogDerivativeCovarianceMeaningRequiredIsTrue :
      secondLogDerivativeCovarianceMeaningRequired ≡ true
    sourceDifferentiatedLocalizationReproved : Bool
    sourceDifferentiatedLocalizationReprovedIsFalse :
      sourceDifferentiatedLocalizationReproved ≡ false

canonicalRound290Boundary : Round290Boundary
canonicalRound290Boundary =
  round290-boundary false refl true refl true refl false refl

round290SourceDifferentiatedLocalizationLevel : ProofLevel
round290SourceDifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round290TwoJSourceSemanticCompilerLevel : ProofLevel
round290TwoJSourceSemanticCompilerLevel = machineChecked

round290PhysicalObservableJCoordinateMeaningLevel : ProofLevel
round290PhysicalObservableJCoordinateMeaningLevel = conditional
