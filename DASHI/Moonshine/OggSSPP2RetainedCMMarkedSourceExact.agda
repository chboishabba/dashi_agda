module DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact where

------------------------------------------------------------------------
-- p=2 RETAINED-ORIENTATION GAUSSIAN-CM MARKED SOURCE
--
-- DASHI FORMAL RECONSTRUCTION
--
-- The source socket requires an actual marked carrier with ten connected
-- components.  We construct a distinct typed carrier
--
--     P2CMMarkedState = CMOrientation x NineOrbit
--
-- where CMOrientation is NOT definitionally the target StrictSignedSide.
-- The source groupoid is discrete, so all ten marked states remain distinct.
--
-- We then prove an exact two-sided recognition into the canonical retained-
-- orientation residual carrier
--
--     StrictSignedSide x NineOrbit.
--
-- Existing p2 receipts calibrate the lane as F4/F2, Frobenius C2, j=1728,
-- Gaussian CM, conductor/level 4.  They do not identify this DASHI ten-state
-- reconstruction with the classical modular-curve marked-point set; that
-- external identification remains separately uninhabited.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact as Socket
import DASHI.Physics.Closure.P2LaneInnerProductProof as Receipt
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Distinct source-native marked carrier.
------------------------------------------------------------------------

data CMOrientation : Set where
  cmLower : CMOrientation
  cmUpper : CMOrientation

record P2CMMarkedState : Set where
  constructor cm-marked-state
  field
    orientation : CMOrientation
    innerOrbit : Triadic.NineOrbit

open P2CMMarkedState public

cmOrientationToSide :
  CMOrientation ->
  Compression.StrictSignedSide
cmOrientationToSide cmLower = Compression.lowerSide
cmOrientationToSide cmUpper = Compression.upperSide

sideToCMOrientation :
  Compression.StrictSignedSide ->
  CMOrientation
sideToCMOrientation Compression.lowerSide = cmLower
sideToCMOrientation Compression.upperSide = cmUpper

cmOrientationRoundTrip :
  (orientation : CMOrientation) ->
  sideToCMOrientation (cmOrientationToSide orientation) ≡ orientation
cmOrientationRoundTrip cmLower = refl
cmOrientationRoundTrip cmUpper = refl

sideRoundTrip :
  (side : Compression.StrictSignedSide) ->
  cmOrientationToSide (sideToCMOrientation side) ≡ side
sideRoundTrip Compression.lowerSide = refl
sideRoundTrip Compression.upperSide = refl

toResidual :
  P2CMMarkedState ->
  Target.P2ResidualObject
toResidual state =
  cmOrientationToSide (orientation state) , innerOrbit state

fromResidual :
  Target.P2ResidualObject ->
  P2CMMarkedState
fromResidual (side , orbit) =
  cm-marked-state (sideToCMOrientation side) orbit

sourceTargetRoundTrip :
  (state : P2CMMarkedState) ->
  fromResidual (toResidual state) ≡ state
sourceTargetRoundTrip (cm-marked-state cmLower orbit) = refl
sourceTargetRoundTrip (cm-marked-state cmUpper orbit) = refl

targetSourceRoundTrip :
  (state : Target.P2ResidualObject) ->
  toResidual (fromResidual state) ≡ state
targetSourceRoundTrip (Compression.lowerSide , orbit) = refl
targetSourceRoundTrip (Compression.upperSide , orbit) = refl

toResidualInjective :
  {left right : P2CMMarkedState} ->
  toResidual left ≡ toResidual right ->
  left ≡ right
toResidualInjective {left} {right} same =
  trans
    (sym (sourceTargetRoundTrip left))
    (trans
      (cong fromResidual same)
      (sourceTargetRoundTrip right))

------------------------------------------------------------------------
-- 2. Discrete ten-component source action groupoid.
------------------------------------------------------------------------

unitCombine : ⊤ -> ⊤ -> ⊤
unitCombine tt tt = tt

unitInverse : ⊤ -> ⊤
unitInverse tt = tt

actCM :
  ⊤ ->
  P2CMMarkedState ->
  P2CMMarkedState
actCM tt state = state

identityActs :
  (state : P2CMMarkedState) ->
  actCM tt state ≡ state
identityActs state = refl

combineActs :
  (g h : ⊤) ->
  (state : P2CMMarkedState) ->
  actCM (unitCombine g h) state
  ≡ actCM g (actCM h state)
combineActs tt tt state = refl

inverseLeft :
  (g : ⊤) ->
  (state : P2CMMarkedState) ->
  actCM (unitInverse g) (actCM g state) ≡ state
inverseLeft tt state = refl

inverseRight :
  (g : ⊤) ->
  (state : P2CMMarkedState) ->
  actCM g (actCM (unitInverse g) state) ≡ state
inverseRight tt state = refl

p2CMAction :
  Action.InvertibleSymmetryAction P2CMMarkedState ⊤
p2CMAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    actCM
    identityActs
    combineActs
    inverseLeft
    inverseRight

p2CMOrbitPresentation :
  Orbit.OrbitPresentation p2CMAction
p2CMOrbitPresentation =
  Orbit.orbitPresentation
    P2CMMarkedState
    (λ state -> state)
    (λ state -> state)
    (λ tt state -> refl)
    (λ state -> refl)
    (λ state -> tt)
    (λ state -> refl)

------------------------------------------------------------------------
-- 3. Coarse-j and socket inhabitant.
------------------------------------------------------------------------

p2CMCoarseJ :
  P2CMMarkedState ->
  ⊤
p2CMCoarseJ state = tt

p2CMCoarseJConstant :
  (state : P2CMMarkedState) ->
  p2CMCoarseJ state ≡ tt
p2CMCoarseJConstant state = refl

canonicalP2MarkedArithmeticSource :
  Socket.P2MarkedArithmeticSource
canonicalP2MarkedArithmeticSource =
  record
    { MarkedState = P2CMMarkedState
    ; Symmetry = ⊤
    ; action = p2CMAction
    ; orbits = p2CMOrbitPresentation
    ; coarseJ = p2CMCoarseJ
    ; coarseJConstant = p2CMCoarseJConstant
    ; markedResidualStructurePresent = true
    ; markedResidualStructurePresentIsTrue = refl
    }

p2CMProvenance :
  P2CMMarkedState ->
  Socket.P2CMProvenance
p2CMProvenance state =
  Socket.gaussianCMJ1728LevelFour

p2CMProvenanceConstant :
  (state : P2CMMarkedState) ->
  p2CMProvenance state ≡ Socket.gaussianCMJ1728LevelFour
p2CMProvenanceConstant state = refl

canonicalP2MarkedLevelCMSource :
  Socket.P2MarkedLevelCMSource
canonicalP2MarkedLevelCMSource =
  record
    { baseSource =
        canonicalP2MarkedArithmeticSource
    ; cmProvenance =
        p2CMProvenance
    ; cmProvenanceConstant =
        p2CMProvenanceConstant
    ; receiptF4F2Calibration =
        Receipt.p2LaneInnerProductRecordsF4F2
    ; receiptFrobeniusC2Calibration =
        Receipt.p2LaneInnerProductRecordsFrobeniusC2
    ; receiptGaussianCMLevelFourCalibration =
        Receipt.p2LaneInnerProductRecordsGaussianCMLevelFour
    ; actualMarkedLevelCMCarrierSupplied =
        true
    ; actualMarkedLevelCMCarrierSuppliedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 4. Exact recognition into retained-orientation residual target.
------------------------------------------------------------------------

p2CMToResidualActionRecognition :
  Recognition.ActionRecognitionFunctor
    p2CMAction
    Target.p2DiscreteAction
p2CMToResidualActionRecognition =
  Recognition.action-recognition-functor
    toResidual
    (λ tt -> tt)
    refl
    (λ tt tt -> refl)
    (λ tt -> refl)
    (λ tt state -> refl)

p2CMToResidualOrbitRecognition :
  Recognition.OrbitRecognition
    p2CMToResidualActionRecognition
    p2CMOrbitPresentation
    Target.p2DiscreteOrbitPresentation
p2CMToResidualOrbitRecognition =
  Recognition.orbit-recognition
    toResidual
    (λ state -> refl)

p2CMToResidualPi0Embedding :
  Recognition.Pi0Embedding p2CMToResidualOrbitRecognition
p2CMToResidualPi0Embedding =
  Recognition.pi0-embedding
    toResidualInjective

p2CMToResidualPi0Surjection :
  Recognition.Pi0Surjection p2CMToResidualOrbitRecognition
p2CMToResidualPi0Surjection =
  Recognition.pi0-surjection
    fromResidual
    targetSourceRoundTrip

p2CMToResidualStabilizerRecognition :
  Recognition.StabilizerRecognition p2CMToResidualOrbitRecognition
p2CMToResidualStabilizerRecognition =
  Recognition.stabilizer-recognition
    (λ state -> refl)
    (λ state tt same -> refl)
    (λ state tt same -> refl)

p2CMToResidualFullRecognition :
  Recognition.OrbitStabilizerRecognition
    p2CMToResidualActionRecognition
    p2CMOrbitPresentation
    Target.p2DiscreteOrbitPresentation
p2CMToResidualFullRecognition =
  Recognition.orbit-stabilizer-recognition
    p2CMToResidualOrbitRecognition
    p2CMToResidualPi0Embedding
    p2CMToResidualPi0Surjection
    p2CMToResidualStabilizerRecognition

------------------------------------------------------------------------
-- 5. External-moduli identification firewall.
------------------------------------------------------------------------

data ExternalClassicalX04IdentifiesP2CMMarkedState : Set where

externalClassicalX04IdentificationStillOpen :
  ExternalClassicalX04IdentifiesP2CMMarkedState -> ⊥
externalClassicalX04IdentificationStillOpen ()

data ReceiptCalibrationCreatesTenStateClassification : Set where

receiptCalibrationDoesNotCreateTenStateClassification :
  ReceiptCalibrationCreatesTenStateClassification -> ⊥
receiptCalibrationDoesNotCreateTenStateClassification ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2RetainedCMMarkedSourceBoundary : Set where
  constructor p2-retained-cm-marked-source-boundary
  field
    distinctTypedTenStateCarrierConstructed : Bool
    discreteTenComponentGroupoidConstructed : Bool
    genericArithmeticSocketInhabited : Bool
    markedLevelCMSourceSocketInhabited : Bool
    exactTwoSidedResidualRecognitionProved : Bool
    receiptF4F2CalibrationConsumed : Bool
    receiptGaussianCMLevelFourCalibrationConsumed : Bool
    repositoryFormalReconstruction : Bool
    externalClassicalX04IdentificationPaid : Bool
    receiptAloneClassifiesTenMarkedStates : Bool

canonicalP2RetainedCMMarkedSourceBoundary :
  P2RetainedCMMarkedSourceBoundary
canonicalP2RetainedCMMarkedSourceBoundary =
  p2-retained-cm-marked-source-boundary
    true true true true true true true true false false
