module DASHI.Physics.Plasma.TriadicPhaseFourierProjectorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Base369BinaryTernaryRefinement as R23

------------------------------------------------------------------------
-- TRIADIC PHASE FOURIER PROJECTOR
--
-- Equal averaging over C_N phases acts as a discrete Fourier projector:
-- angular harmonics not divisible by N cancel, while harmonics divisible by N
-- survive.  This owner records the exact phase-resolution arithmetic and keeps
-- the analytic roots-of-unity identity as an explicit receipt until welded to a
-- concrete complex/Fourier carrier.
------------------------------------------------------------------------

pureTriadicResolution : Nat → R23.Resolution23
pureTriadicResolution n = R23.resolution23 0 (suc n)

pureTriadicSectorCount : Nat → Nat
pureTriadicSectorCount n = R23.sectorCount (pureTriadicResolution n)

triadic0Count : pureTriadicSectorCount 0 ≡ 3
triadic0Count = refl

triadic1Count : pureTriadicSectorCount 1 ≡ 9
triadic1Count = refl

triadic2Count : pureTriadicSectorCount 2 ≡ 27
triadic2Count = refl

record CyclicFourierProjectorReceipt : Set₁ where
  constructor cyclic-fourier-projector-receipt
  field
    ternaryDepth : Nat
    sectorCount : Nat
    sectorCountMatchesTriadicResolution :
      sectorCount ≡ pureTriadicSectorCount ternaryDepth

    Harmonic : Set
    phaseAverage : Harmonic → Set
    survives : Harmonic → Set
    killed : Harmonic → Set

    rootsOfUnityFilterReceipt : Set
    nonMultipleHarmonicsKilledReceipt : Set
    multipleHarmonicsSurviveReceipt : Set
    sameObservableAcrossPhaseSamplesReceipt : Set
    projectorReference : String

open CyclicFourierProjectorReceipt public

record TriadicProjectorBoundary : Set where
  constructor triadic-projector-boundary
  field
    phaseAveragingIsPhysicalFieldSuperpositionByDefinition : Bool
    phaseAveragingIsPhysicalFieldSuperpositionByDefinitionIsFalse :
      phaseAveragingIsPhysicalFieldSuperpositionByDefinition ≡ false

    rootsOfUnityProjectorMayShapeGeometrySearch : Bool
    rootsOfUnityProjectorMayShapeGeometrySearchIsTrue :
      rootsOfUnityProjectorMayShapeGeometrySearch ≡ true

    c9AutomaticallyBeatsC3ForEveryPhysicalObservable : Bool
    c9AutomaticallyBeatsC3ForEveryPhysicalObservableIsFalse :
      c9AutomaticallyBeatsC3ForEveryPhysicalObservable ≡ false

canonicalTriadicProjectorBoundary : TriadicProjectorBoundary
canonicalTriadicProjectorBoundary =
  triadic-projector-boundary false refl true refl false refl

localProjectorProbeReference : String
localProjectorProbeReference =
  "scripts/triadic_phase_projector_probe.py / scripts/test_triadic_phase_projector_probe.py"
