module DASHI.Physics.Astrophysics.GrillmairStellarStreamSourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact as Base

record GrillmairStreamReplay : Set where
  constructor grillmair-stream-replay
  field
    sourceReference : String
    candidateNames : String
    approximateDistanceKpc : Nat
    angularLengthDegMin angularLengthDegMax : Nat
    physicalLengthKpcMin physicalLengthKpcMax : Nat
    widthPcMin widthPcMax : Nat
    estimatedStarsMin estimatedStarsMax : Nat
    molongloAtlasOffsetTenthsDeg : Nat
    exactCatalogueSlicePaid : Bool
    exactMatchedFilterWeightsPaid : Bool
    orbitUncertaintyPaid : Bool

open GrillmairStreamReplay public

grillmairStreamReplay : GrillmairStreamReplay
grillmairStreamReplay = grillmair-stream-replay
  "Grillmair 2017, ApJ 847:119, DOI 10.3847/1538-4357/aa8872; arXiv:1708.09029"
  "Murrumbidgee; Molonglo; Orinoco; Kwando"
  20
  13 95
  5 33
  100 300
  3000 8000
  25
  false false false

baseObservation : Base.StreamObservation
baseObservation = Base.southCapCandidates

abstractPaysFiniteEnsembleGeometry : Bool
abstractPaysFiniteEnsembleGeometry = true

ensembleGeometryPaysUniqueOrbit : Bool
ensembleGeometryPaysUniqueOrbit = false

molongloAtlasProximityPaysCommonOrigin : Bool
molongloAtlasProximityPaysCommonOrigin = false
