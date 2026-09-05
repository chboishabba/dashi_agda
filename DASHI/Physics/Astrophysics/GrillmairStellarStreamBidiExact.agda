module DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.FiniteObservationClosureBidiExact as Closure

-- Grillmair 2017, ApJ 847:119, DOI 10.3847/1538-4357/aa8872.

data StreamCandidate : Set where murrumbidgee molonglo orinoco kwando : StreamCandidate

record StreamObservation : Set where
  constructor stream-observation
  field
    candidate : StreamCandidate
    distanceKpcApprox : ℕ
    angularLengthDegMin angularLengthDegMax : ℕ
    physicalWidthPcMin physicalWidthPcMax : ℕ
    sourceReference : String

open StreamObservation public

southCapCandidates : StreamObservation
southCapCandidates = stream-observation molonglo 20 13 95 100 300
  "Grillmair 2017: four cold stellar-stream candidates in Pan-STARRS; ensemble ranges"

record StellarStreamBoundary : Set where
  constructor stellar-stream-boundary
  field
    overdensityAutomaticallyProvesBoundStream : Bool
    overdensityAutomaticallyProvesBoundStreamIsFalse : overdensityAutomaticallyProvesBoundStream ≡ false
    projectedTrackUniquelyDeterminesOrbit : Bool
    projectedTrackUniquelyDeterminesOrbitIsFalse : projectedTrackUniquelyDeterminesOrbit ≡ false
    similarTracksProveCommonProgenitor : Bool
    similarTracksProveCommonProgenitorIsFalse : similarTracksProveCommonProgenitor ≡ false
    streamGeometryCanConstrainGalacticPotential : Bool
    streamGeometryCanConstrainGalacticPotentialIsTrue : streamGeometryCanConstrainGalacticPotential ≡ true

canonicalStellarStreamBoundary : StellarStreamBoundary
canonicalStellarStreamBoundary = stellar-stream-boundary false refl false refl false refl true refl

grillmairOrbitReverse : Closure.ReverseClosureObligation
grillmairOrbitReverse = Closure.reverse-closure-obligation
  "Galactic stellar streams"
  "projected old metal-poor stellar overdensity / stream track"
  "distance, kinematics and Galactic-potential model"
  "orbit/progenitor inference"
  "unique dark-matter distribution from morphology alone"
