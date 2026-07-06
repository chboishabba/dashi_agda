module DASHI.Physics.Closure.NSTriadKNGate2SampledFactorRouteWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.NSTriadKNGate2ASampledComparisonEnvelope
  using ( SampledShell
        ; ScaledRatio
        ; canonicalSampledShells
        ; rhoN
        ; directionalTheta
        ; mulRatio
        ; directionalTransportFactor
        ; directionalProductUpper
        ; directionalProductRouteBelowQuarter
        ; directionalBeatsShellwiseCoarse
        ; directionalFactorBeatsShellwiseCoarseFactor
        ; shellwiseCoarseFactor
        ; shellwiseCoarseTransport
        ; shellwiseCoarseRouteCloses
        ; directionalProductMatchesTheta
        ; shellwiseCoarseFactorReconstructsTransport
        ; sampledDirectionalProductRouteBelowQuarter
        ; sampledDirectionalBeatsShellwiseCoarse
        ; sampledDirectionalFactorBeatsShellwiseCoarseFactor
        ; sampledShellwiseCoarseRouteRejected
        )

----------------------------------------------------------------------
-- Sampled factor-route witness package.
--
-- This is the concrete theorem-facing witness for the live sampled Gate 2
-- route on N = 6, 8, 10.  It does not claim the true NS carrier theorem.
-- It records that, shellwise, the directional factor route reconstructs the
-- sampled transported ratio, beats the shellwise coarse factor, stays below
-- the quarter target, and the shellwise coarse route fails.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Sampled factor-route witness package: on shells N=6,8,10 the directional transported product exactly reconstructs the sampled extremizer-aware ratio, the directional factor is no larger than the shellwise coarse factor, the directional product stays subquarter, and the shellwise coarse transport route fails."

record SampledFactorRouteWitness : Set where
  constructor mkSampledFactorRouteWitness
  field
    shell : SampledShell
    seamRayleighRatio : ScaledRatio
    directionalFactor : ScaledRatio
    directionalTransport : ScaledRatio
    coarseFactor : ScaledRatio
    coarseTransport : ScaledRatio

open SampledFactorRouteWitness public

mulCoarseFactorWithSeam : SampledShell → ScaledRatio
mulCoarseFactorWithSeam s =
  mulRatio (shellwiseCoarseFactor s) (rhoN s)

sampledFactorRouteRow : SampledShell → SampledFactorRouteWitness
sampledFactorRouteRow s =
  mkSampledFactorRouteWitness
    s
    (rhoN s)
    (directionalTransportFactor s)
    (directionalTheta s)
    (shellwiseCoarseFactor s)
    (shellwiseCoarseTransport s)

record NSTriadKNGate2SampledFactorRouteWitnessPackage : Setω where
  constructor mkNSTriadKNGate2SampledFactorRouteWitnessPackage
  field
    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    sampledShells :
      List SampledShell
    sampledShellsAreCanonical :
      sampledShells ≡ canonicalSampledShells

    row : SampledShell → SampledFactorRouteWitness
    rowIsCanonical :
      row ≡ sampledFactorRouteRow

    directionalTransportReconstructs :
      (s : SampledShell) →
      directionalProductUpper s ≡ directionalTheta s

    coarseTransportReconstructs :
      (s : SampledShell) →
      mulCoarseFactorWithSeam s ≡ shellwiseCoarseTransport s

    directionalFactorBeatsCoarseFactor :
      (s : SampledShell) →
      directionalFactorBeatsShellwiseCoarseFactor s ≡ true

    directionalTransportBeatsCoarse :
      (s : SampledShell) →
      directionalBeatsShellwiseCoarse s ≡ true

    directionalTransportSubquarter :
      (s : SampledShell) →
      directionalProductRouteBelowQuarter s ≡ true

    shellwiseCoarseRouteRejected :
      (s : SampledShell) →
      shellwiseCoarseRouteCloses s ≡ false

    packageInstalled : Bool
    packageInstalledIsTrue :
      packageInstalled ≡ true

    sampledWitnessOnly : Bool
    sampledWitnessOnlyIsTrue :
      sampledWitnessOnly ≡ true

    trueCarrierTheoremProved : Bool
    trueCarrierTheoremProvedIsFalse :
      trueCarrierTheoremProved ≡ false

open NSTriadKNGate2SampledFactorRouteWitnessPackage public

canonicalCoarseTransportReconstructs :
  (s : SampledShell) →
  mulCoarseFactorWithSeam s ≡ shellwiseCoarseTransport s
canonicalCoarseTransportReconstructs =
  shellwiseCoarseFactorReconstructsTransport

canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage :
  NSTriadKNGate2SampledFactorRouteWitnessPackage
canonicalNSTriadKNGate2SampledFactorRouteWitnessPackage =
  mkNSTriadKNGate2SampledFactorRouteWitnessPackage
    "Sampled factor-route witness package: on shells N=6,8,10 the directional transported product exactly reconstructs the sampled extremizer-aware ratio, the directional factor is no larger than the shellwise coarse factor, the directional product stays subquarter, and the shellwise coarse transport route fails."
    refl
    canonicalSampledShells
    refl
    sampledFactorRouteRow
    refl
    directionalProductMatchesTheta
    canonicalCoarseTransportReconstructs
    sampledDirectionalFactorBeatsShellwiseCoarseFactor
    sampledDirectionalBeatsShellwiseCoarse
    sampledDirectionalProductRouteBelowQuarter
    sampledShellwiseCoarseRouteRejected
    true
    refl
    true
    refl
    false
    refl
