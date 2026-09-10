{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound287Exact where

------------------------------------------------------------------------
-- ROUND287 / NORMALIZE THE LAST DIRECT-CMP116 B1 SOURCE SEAM
--
-- R284 reduces continuum clustering to one finite source theorem. R274 names
-- that theorem as two literal physical J insertions obeying the CMP116 rooted
-- connecting-shell bound. CMP116 differentiated localization is already
-- source-owned for any finite number of declared source derivatives.
--
-- Therefore do not schedule a fresh clustering theorem. Factor the remaining
-- physical work into exact source-coordinate semantics:
--
--   observable F <-> literal CMP116 J direction jF
--   observable G <-> literal CMP116 J direction jG
--   D^2_{jG,jF} log Z = connected covariance(F,G)
--
-- on the SAME finite state/domain. Once the exact selected source directions
-- are inside the common positive analytic domain, source differentiation keeps
-- the rooted exponential majorant.
------------------------------------------------------------------------

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

record Round287Boundary : Set where
  constructor round287-boundary
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

canonicalRound287Boundary : Round287Boundary
canonicalRound287Boundary =
  round287-boundary false refl true refl true refl false refl

round287SourceDifferentiatedLocalizationLevel : ProofLevel
round287SourceDifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round287TwoJSourceSemanticCompilerLevel : ProofLevel
round287TwoJSourceSemanticCompilerLevel = machineChecked

round287PhysicalObservableJCoordinateMeaningLevel : ProofLevel
round287PhysicalObservableJCoordinateMeaningLevel = conditional
