module DASHI.Interop.SeaMeInItBT369SphereUnwrap where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Fin using (Fin)
open import Data.Nat using (_≤_)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Interop.SeaMeInItROMKernelFormalism
  using (TriGate; gateAdmissible; PromotionState)

------------------------------------------------------------------------
-- Sphere BT369 unwrap as a benchmark-gated approximation surface
------------------------------------------------------------------------

data ProjectionPolicy : Set where
  equalAreaInversePullback : ProjectionPolicy

data SurfaceBasisPolicy : Set where
  triadicSphericalBT369 : SurfaceBasisPolicy
  sphericalHarmonicBasis : SurfaceBasisPolicy
  diffusionWaveletBasis : SurfaceBasisPolicy
  learnedPCABasis : SurfaceBasisPolicy

data CandidateStrategy : Set where
  bootstrapProjection : CandidateStrategy
  lscmCandidate : CandidateStrategy
  equirectCandidate : CandidateStrategy
  equalAreaCandidate : CandidateStrategy
  graphUltrametricCandidate : CandidateStrategy

data SeamGenerator : Set where
  wrapEW : SeamGenerator
  poleNorthTurn : SeamGenerator
  poleSouthTurn : SeamGenerator
  chartTransition : SeamGenerator
  tangentFlip : SeamGenerator
  orientationTurn : SeamGenerator

data NonIsometryBoundaryTag : Set where
  noGlobalSpherePlaneIsometryClaim : NonIsometryBoundaryTag
  benchmarkSliceOnlyClaim : NonIsometryBoundaryTag
  rectangleIsSerializationNotGeometry : NonIsometryBoundaryTag
  correspondenceNotMathematicalInverse : NonIsometryBoundaryTag

record SphereUnwrapCandidate : Set₁ where
  field
    Atlas : Set
    Rect : Set
    unwrap : Atlas → Rect
    residual : Atlas → Nat
    areaError : Nat
    edgeError : Nat
    angleError : Nat
    foldovers : Nat
    agreementDepth : Nat
    score : Nat
    strategy : CandidateStrategy
    projection : ProjectionPolicy
    surfaceBasis : SurfaceBasisPolicy

open SphereUnwrapCandidate public

record BT369Carrier (candidate : SphereUnwrapCandidate) : Set₁ where
  field
    trit : Atlas candidate → Trit
    orientation6 : Atlas candidate → Fin 6
    neighbourhood9 : Atlas candidate → Vec (Atlas candidate) 9
    address3 : Atlas candidate → List Trit
    seamLedger : Atlas candidate → List SeamGenerator

open BT369Carrier public

record BenchmarkScore (candidate : SphereUnwrapCandidate) : Set where
  field
    scoreValue : Nat
    scoreMatchesCandidate : scoreValue ≡ score candidate
    noFoldover : foldovers candidate ≡ zero

open BenchmarkScore public

record DeclaredBenchmarkSlice : Set₁ where
  field
    candidateInSlice : SphereUnwrapCandidate → Set
    containsBootstrap : Set
    containsLSCM : Set
    containsGraphUltrametric : Set
    scoreLowerIsBetter : Bool

open DeclaredBenchmarkSlice public

record WinsBenchmark
    (winner : SphereUnwrapCandidate)
    (slice : DeclaredBenchmarkSlice) : Set₁ where
  field
    winnerInSlice : candidateInSlice slice winner
    lowerOrEqual :
      (candidate : SphereUnwrapCandidate) →
      candidateInSlice slice candidate →
      score winner ≤ score candidate

open WinsBenchmark public

record NonIsometryBoundary (candidate : SphereUnwrapCandidate) : Set₁ where
  field
    tags : List NonIsometryBoundaryTag
    notGlobalIsometryClaim : Set
    benchmarkOnlyClaim : Set
    rectangleOnlySerialization : Set

open NonIsometryBoundary public

record BT369SphereUnwrapCertificate
    (candidate : SphereUnwrapCandidate) : Set₁ where
  field
    residualLInf : Nat
    residualL2AreaWeighted : Nat
    tritHistogram : Trit → Nat
    depthHistogram : Nat → Nat
    seamBraidCounts : SeamGenerator → Nat
    missingCoverage : Nat
    multiHitCoverage : Nat
    coverageGate : TriGate
    residualGate : TriGate
    agreementGate : TriGate
    benchmarkGate : TriGate
    certificateHash : String

open BT369SphereUnwrapCertificate public

record SphereBT369UnwrapReceipt : Set₁ where
  field
    candidate : SphereUnwrapCandidate
    carrier : BT369Carrier candidate
    declaredSlice : DeclaredBenchmarkSlice
    benchmarkWin : WinsBenchmark candidate declaredSlice
    nonIsometry : NonIsometryBoundary candidate
    certificate : BT369SphereUnwrapCertificate candidate
    promotionState : PromotionState
    plainReading : String

open SphereBT369UnwrapReceipt public

record PromotionGate
    (receipt : SphereBT369UnwrapReceipt) : Set where
  field
    noMissingCoverage :
      missingCoverage (certificate receipt) ≡ zero
    noMultiHitCoverage :
      multiHitCoverage (certificate receipt) ≡ zero
    zeroFoldovers :
      foldovers (candidate receipt) ≡ zero
    coveragePromoted :
      coverageGate (certificate receipt) ≡ gateAdmissible
    residualPromoted :
      residualGate (certificate receipt) ≡ gateAdmissible
    agreementPromoted :
      agreementGate (certificate receipt) ≡ gateAdmissible
    benchmarkPromoted :
      benchmarkGate (certificate receipt) ≡ gateAdmissible

open PromotionGate public

record BenchmarkBoundaryStatement
    (receipt : SphereBT369UnwrapReceipt) : Set₁ where
  field
    checkedClaim :
      WinsBenchmark (candidate receipt) (declaredSlice receipt)
    excludedClaim :
      NonIsometryBoundary (candidate receipt)
    summary :
      String

open BenchmarkBoundaryStatement public
