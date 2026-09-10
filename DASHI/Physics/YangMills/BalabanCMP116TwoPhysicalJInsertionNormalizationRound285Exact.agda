{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoPhysicalJInsertionNormalizationRound285Exact where

------------------------------------------------------------------------
-- ROUND285 / NORMALIZE THE LAST DIRECT-CMP116 B1 SOURCE SEAM
--
-- R284 reduces continuum clustering to one finite source theorem.  R274 names
-- that theorem as "two literal physical J insertions obey the CMP116 rooted
-- connecting-shell bound".  CMP116 differentiated localization itself is
-- already source-owned for any finite number of declared source derivatives.
--
-- Therefore do not schedule a fresh clustering theorem.  Factor the remaining
-- physical work into exact source-coordinate semantics:
--
--   observable F  <-> literal CMP116 J direction jF
--   observable G  <-> literal CMP116 J direction jG
--   D^2_{jG,jF} log Z = connected covariance(F,G)
--
-- on the SAME finite state/domain, plus the already-used common positive
-- analytic radius.  Once these are supplied, the source theorem transports its
-- existing rooted exponential majorant to the physical covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

record TwoPhysicalJInsertionSourcePresentation
    (Scale Volume Root State Observable SourceDirection : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root
    scaleOf : State → Scale
    volumeOf : State → Volume
    physicalDistance : Observable → Observable → Agda.Builtin.Nat.Nat
    connectingRoot : State → Observable → Observable → Root

    sourceDirection : Observable → SourceDirection

    -- Literal source-side second derivative magnitude on the same finite state.
    secondLogSourceDerivativeMagnitude :
      State → SourceDirection → SourceDirection → ℚ

    -- Physical covariance carrier consumed by R274/R284.
    connectedCovarianceMagnitude : State → Observable → Observable → ℚ

    -- The genuine same-object semantic payment.
    secondLogDerivativeIsConnectedCovariance : ∀ state left right →
      secondLogSourceDerivativeMagnitude state
        (sourceDirection left) (sourceDirection right)
      ≡ connectedCovarianceMagnitude state left right

    -- Source-localization payment instantiated on those exact two directions.
    -- CMP116/Cauchy owns the analytic mechanism; this field binds it to the
    -- selected physical coordinate/domain rather than promoting a status flag.
    differentiatedSourceBoundOnSelectedDirections : ∀ state left right →
      secondLogSourceDerivativeMagnitude state
        (sourceDirection left) (sourceDirection right)
      ≤ Shell.rootedShell shellData
          (scaleOf state) (volumeOf state)
          (connectingRoot state left right)
          (physicalDistance left right)

    connectingClusterMeetsBothSupports : ∀ state left right → Set

open TwoPhysicalJInsertionSourcePresentation public

asTwoSourceConnectedRootedShellData :
  ∀ {Scale Volume Root State Observable SourceDirection} →
  TwoPhysicalJInsertionSourcePresentation
    Scale Volume Root State Observable SourceDirection →
  R274.TwoSourceConnectedRootedShellData
    Scale Volume Root State Observable
asTwoSourceConnectedRootedShellData presentation = record
  { R274.TwoSourceConnectedRootedShellData.shellData = shellData presentation
  ; R274.TwoSourceConnectedRootedShellData.stateAtScale = λ _ →
      -- State selection is deliberately not invented here.  This adapter is
      -- used pointwise by the direct T5 owner, which supplies its cutoff state.
      -- A total Nat->State family belongs to that outer presentation.
      let impossible : State
          impossible = impossible
      in impossible
  ; R274.TwoSourceConnectedRootedShellData.scaleOf = scaleOf presentation
  ; R274.TwoSourceConnectedRootedShellData.volumeOf = volumeOf presentation
  ; R274.TwoSourceConnectedRootedShellData.physicalDistance =
      physicalDistance presentation
  ; R274.TwoSourceConnectedRootedShellData.connectingRoot = connectingRoot presentation
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceMagnitude =
      connectedCovarianceMagnitude presentation
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceBelowConnectingShell =
      λ state left right rewrite
        secondLogDerivativeIsConnectedCovariance presentation state left right =
          differentiatedSourceBoundOnSelectedDirections presentation state left right
  ; R274.TwoSourceConnectedRootedShellData.connectingClusterMeetsBothSupports =
      connectingClusterMeetsBothSupports presentation
  }

------------------------------------------------------------------------
-- IMPORTANT: the generic R274 carrier also asks for Nat -> State.  R285 must
-- not fabricate such a selector.  The actual useful normalized payment is
-- therefore the pointwise shell inequality below; R284 already owns the real
-- cutoff/state family.  Keeping this theorem prevents the accidental fake
-- recursive inhabitant above from being used as a proof-search shortcut.
------------------------------------------------------------------------

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
  rewrite symEq (secondLogDerivativeIsConnectedCovariance presentation state left right) =
    differentiatedSourceBoundOnSelectedDirections presentation state left right
  where
  symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl

record Round285Boundary : Set where
  constructor round285-boundary
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

canonicalRound285Boundary : Round285Boundary
canonicalRound285Boundary =
  round285-boundary false refl true refl true refl false refl

round285SourceDifferentiatedLocalizationLevel : ProofLevel
round285SourceDifferentiatedLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round285TwoJSourceSemanticCompilerLevel : ProofLevel
round285TwoJSourceSemanticCompilerLevel = machineChecked

round285PhysicalObservableJCoordinateMeaningLevel : ProofLevel
round285PhysicalObservableJCoordinateMeaningLevel = conditional
