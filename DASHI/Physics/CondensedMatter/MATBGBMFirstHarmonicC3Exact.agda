module DASHI.Physics.CondensedMatter.MATBGBMFirstHarmonicC3Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twistronics
import DASHI.Physics.CondensedMatter.MATBG2026VerticalSliceExact as MATBG

open MATBG public using (Valley; K; KPrime; timeReverseValley)

------------------------------------------------------------------------
-- BISTRITZER–MACDONALD FIRST-HARMONIC C3 PHASE SKELETON
--
-- Source role: Bistritzer & MacDonald (2011), already attributed by the
-- Twistronics owner, supplies the continuum-model / three first-harmonic
-- interlayer-coupling architecture.  This DASHI owner formalizes the exact
-- symbolic phase and 2x2 tunnelling-matrix skeleton in a declared convention:
--
--   T_j(v) = [ w0, w1 * u(v,j) ; w1 * conjugate(u(v,j)), w0 ]
--
-- with j in three C3-related moire harmonics and the two valleys related by
-- complex conjugation.  C3Phase is a symbolic third-root carrier; this owner
-- does not claim a calibrated complex-number Hamiltonian, continuum momentum
-- truncation, interacting self-energy, or fitted sample parameters.
------------------------------------------------------------------------

data MoireHarmonic : Set where
  harmonic0 harmonic1 harmonic2 : MoireHarmonic

rotateHarmonic : MoireHarmonic → MoireHarmonic
rotateHarmonic harmonic0 = harmonic1
rotateHarmonic harmonic1 = harmonic2
rotateHarmonic harmonic2 = harmonic0

rotateHarmonicCubed :
  (h : MoireHarmonic) →
  rotateHarmonic (rotateHarmonic (rotateHarmonic h)) ≡ h
rotateHarmonicCubed harmonic0 = refl
rotateHarmonicCubed harmonic1 = refl
rotateHarmonicCubed harmonic2 = refl

------------------------------------------------------------------------
-- Convention-explicit off-diagonal phase table.
------------------------------------------------------------------------

upperOffDiagonalPhase : Valley → MoireHarmonic → C3.C3Phase
upperOffDiagonalPhase K harmonic0 = C3.phase0
upperOffDiagonalPhase K harmonic1 = C3.phase2
upperOffDiagonalPhase K harmonic2 = C3.phase1
upperOffDiagonalPhase KPrime harmonic0 = C3.phase0
upperOffDiagonalPhase KPrime harmonic1 = C3.phase1
upperOffDiagonalPhase KPrime harmonic2 = C3.phase2

lowerOffDiagonalPhase : Valley → MoireHarmonic → C3.C3Phase
lowerOffDiagonalPhase v h = C3.conjugatePhase (upperOffDiagonalPhase v h)

lowerIsConjugateUpper :
  (v : Valley) (h : MoireHarmonic) →
  lowerOffDiagonalPhase v h
    ≡ C3.conjugatePhase (upperOffDiagonalPhase v h)
lowerIsConjugateUpper v h = refl

valleyRotationCharacter : Valley → C3.C3Phase
valleyRotationCharacter K = C3.phase2
valleyRotationCharacter KPrime = C3.phase1

upperPhaseRotationLaw :
  (v : Valley) (h : MoireHarmonic) →
  upperOffDiagonalPhase v (rotateHarmonic h)
    ≡ C3.multiplyPhase
        (valleyRotationCharacter v)
        (upperOffDiagonalPhase v h)
upperPhaseRotationLaw K harmonic0 = refl
upperPhaseRotationLaw K harmonic1 = refl
upperPhaseRotationLaw K harmonic2 = refl
upperPhaseRotationLaw KPrime harmonic0 = refl
upperPhaseRotationLaw KPrime harmonic1 = refl
upperPhaseRotationLaw KPrime harmonic2 = refl

timeReversalConjugatesUpper :
  (v : Valley) (h : MoireHarmonic) →
  upperOffDiagonalPhase (timeReverseValley v) h
    ≡ C3.conjugatePhase (upperOffDiagonalPhase v h)
timeReversalConjugatesUpper K harmonic0 = refl
timeReversalConjugatesUpper K harmonic1 = refl
timeReversalConjugatesUpper K harmonic2 = refl
timeReversalConjugatesUpper KPrime harmonic0 = refl
timeReversalConjugatesUpper KPrime harmonic1 = refl
timeReversalConjugatesUpper KPrime harmonic2 = refl

------------------------------------------------------------------------
-- Exact symbolic 2x2 tunnelling matrices.
------------------------------------------------------------------------

data BMSymbolicScalar : Set where
  w0Term : BMSymbolicScalar
  w1PhaseTerm : C3.C3Phase → BMSymbolicScalar

conjugateSymbolicScalar : BMSymbolicScalar → BMSymbolicScalar
conjugateSymbolicScalar w0Term = w0Term
conjugateSymbolicScalar (w1PhaseTerm p) =
  w1PhaseTerm (C3.conjugatePhase p)

record BMSymbolicMatrix2 : Set where
  constructor bm-symbolic-matrix2
  field
    entryAA : BMSymbolicScalar
    entryAB : BMSymbolicScalar
    entryBA : BMSymbolicScalar
    entryBB : BMSymbolicScalar

open BMSymbolicMatrix2 public

tunnellingMatrix : Valley → MoireHarmonic → BMSymbolicMatrix2
tunnellingMatrix v h =
  bm-symbolic-matrix2
    w0Term
    (w1PhaseTerm (upperOffDiagonalPhase v h))
    (w1PhaseTerm (lowerOffDiagonalPhase v h))
    w0Term

conjugateSymbolicMatrix : BMSymbolicMatrix2 → BMSymbolicMatrix2
conjugateSymbolicMatrix (bm-symbolic-matrix2 aa ab ba bb) =
  bm-symbolic-matrix2
    (conjugateSymbolicScalar aa)
    (conjugateSymbolicScalar ab)
    (conjugateSymbolicScalar ba)
    (conjugateSymbolicScalar bb)

advanceUpperScalar : Valley → BMSymbolicScalar → BMSymbolicScalar
advanceUpperScalar v w0Term = w0Term
advanceUpperScalar v (w1PhaseTerm p) =
  w1PhaseTerm (C3.multiplyPhase (valleyRotationCharacter v) p)

advanceLowerScalar : Valley → BMSymbolicScalar → BMSymbolicScalar
advanceLowerScalar v w0Term = w0Term
advanceLowerScalar v (w1PhaseTerm p) =
  w1PhaseTerm
    (C3.multiplyPhase
      (C3.conjugatePhase (valleyRotationCharacter v))
      p)

advanceTunnellingMatrix : Valley → BMSymbolicMatrix2 → BMSymbolicMatrix2
advanceTunnellingMatrix v (bm-symbolic-matrix2 aa ab ba bb) =
  bm-symbolic-matrix2
    aa
    (advanceUpperScalar v ab)
    (advanceLowerScalar v ba)
    bb

tunnellingMatrixTimeReversal :
  (v : Valley) (h : MoireHarmonic) →
  tunnellingMatrix (timeReverseValley v) h
    ≡ conjugateSymbolicMatrix (tunnellingMatrix v h)
tunnellingMatrixTimeReversal K harmonic0 = refl
tunnellingMatrixTimeReversal K harmonic1 = refl
tunnellingMatrixTimeReversal K harmonic2 = refl
tunnellingMatrixTimeReversal KPrime harmonic0 = refl
tunnellingMatrixTimeReversal KPrime harmonic1 = refl
tunnellingMatrixTimeReversal KPrime harmonic2 = refl

tunnellingMatrixC3Covariance :
  (v : Valley) (h : MoireHarmonic) →
  tunnellingMatrix v (rotateHarmonic h)
    ≡ advanceTunnellingMatrix v (tunnellingMatrix v h)
tunnellingMatrixC3Covariance K harmonic0 = refl
tunnellingMatrixC3Covariance K harmonic1 = refl
tunnellingMatrixC3Covariance K harmonic2 = refl
tunnellingMatrixC3Covariance KPrime harmonic0 = refl
tunnellingMatrixC3Covariance KPrime harmonic1 = refl
tunnellingMatrixC3Covariance KPrime harmonic2 = refl

------------------------------------------------------------------------
-- Typed BM block architecture.
------------------------------------------------------------------------

record BMTunnellingBlock : Set where
  constructor bm-tunnelling-block
  field
    valley : Valley
    harmonic : MoireHarmonic
    aaLikeAmplitudeReference : String
    abLikeAmplitudeReference : String
    matrix : BMSymbolicMatrix2
    matrixMatchesConvention : matrix ≡ tunnellingMatrix valley harmonic

open BMTunnellingBlock public

canonicalTunnellingBlock : Valley → MoireHarmonic → BMTunnellingBlock
canonicalTunnellingBlock v h =
  bm-tunnelling-block v h "w0" "w1" (tunnellingMatrix v h) refl

record BMFirstHarmonicHamiltonianContract : Set where
  constructor bm-first-harmonic-hamiltonian-contract
  field
    sourceReference : String
    topDiracBlockReference : String
    bottomDiracBlockReference : String
    momentumRotationReference : String
    interlayerBlock0 : BMTunnellingBlock
    interlayerBlock1 : BMTunnellingBlock
    interlayerBlock2 : BMTunnellingBlock
    threeFirstHarmonicsPresent : Bool
    valleyResolved : Bool
    layerResolved : Bool
    sublatticeResolved : Bool
    symbolicMatrixBackendPaid : Bool
    concreteComplexMatrixBackendPaid : Bool
    sampleParametersPaid : Bool

open BMFirstHarmonicHamiltonianContract public

canonicalKValleyBMContract : BMFirstHarmonicHamiltonianContract
canonicalKValleyBMContract =
  bm-first-harmonic-hamiltonian-contract
    "Bistritzer and MacDonald 2011, DOI 10.1073/pnas.1108174108"
    "rotated monolayer Dirac block for top layer"
    "counter-rotated monolayer Dirac block for bottom layer"
    "three moire momentum-transfer vectors related by C3"
    (canonicalTunnellingBlock K harmonic0)
    (canonicalTunnellingBlock K harmonic1)
    (canonicalTunnellingBlock K harmonic2)
    true true true true true false false

record BMFirstHarmonicBoundary : Set where
  constructor bm-first-harmonic-boundary
  field
    sourceArchitecturePaid : Bool
    exactThreeHarmonicC3PhaseSkeletonPaid : Bool
    exactValleyConjugationPaid : Bool
    exactHarmonicRotationClosurePaid : Bool
    symbolicTwoByTwoMatrixBackendPaid : Bool
    matrixLevelTimeReversalPaid : Bool
    matrixLevelC3CovariancePaid : Bool
    scalarComplexMatrixBackendPaid : Bool
    continuumMomentumLatticePaid : Bool
    sampleParameterCalibrationPaid : Bool
    interactingSelfEnergyPaid : Bool
    qtmForwardModelPaid : Bool
    qtmDataReplayPaid : Bool
    symbolicMatrixIsMeasuredHamiltonian : Bool

open BMFirstHarmonicBoundary public

canonicalBMFirstHarmonicBoundary : BMFirstHarmonicBoundary
canonicalBMFirstHarmonicBoundary =
  bm-first-harmonic-boundary
    true true true true true true true
    false false false false false false false

record BMFirstHarmonicAttributionBoundary : Set where
  constructor bm-first-harmonic-attribution-boundary
  field
    bistritzerMacDonaldOwnsContinuumModelSourceRole : Bool
    dashiOwnsSymbolicC3Formalization : Bool
    symbolicFormalizationDoesNotReattributeExperimentalQTM : Bool
    laterQTMDataDoesNotRetroactivelyBelongToBM2011 : Bool

open BMFirstHarmonicAttributionBoundary public

canonicalBMFirstHarmonicAttributionBoundary : BMFirstHarmonicAttributionBoundary
canonicalBMFirstHarmonicAttributionBoundary =
  bm-first-harmonic-attribution-boundary true true true true
