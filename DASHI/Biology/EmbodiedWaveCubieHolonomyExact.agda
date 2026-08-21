module DASHI.Biology.EmbodiedWaveCubieHolonomyExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- EMBODIED WAVE CUBIE HOLONOMY ANALOGUE
--
-- Kenneth G. Wilson, "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
-- Frank Wilczek; A. Zee,
-- "Appearance of Gauge Structure in Simple Dynamical Systems".
-- DOI: 10.1103/PhysRevLett.52.2111.
--
-- This is a finite order-sensitive cubie model.  Wave-supported accessibility
-- and body regulation preserve the same public surface individually, yet their
-- ordered composite endpoints differ.  No gauge connection, curvature,
-- Wilson loop, clinical treatment law, or quantum brain is asserted.
------------------------------------------------------------------------

data FineEmbodiedWaveState : Set where
  rootState waveShifted bodyShifted waveAfterBody bodyAfterWave : FineEmbodiedWaveState

data PublicSurface : Set where
  samePublicSurface : PublicSurface

projectPublic : FineEmbodiedWaveState → PublicSurface
projectPublic _ = samePublicSurface

waveTransport : FineEmbodiedWaveState → FineEmbodiedWaveState
waveTransport rootState = waveShifted
waveTransport bodyShifted = waveAfterBody
waveTransport state = state

bodyRegulation : FineEmbodiedWaveState → FineEmbodiedWaveState
bodyRegulation rootState = bodyShifted
bodyRegulation waveShifted = bodyAfterWave
bodyRegulation state = state

waveThenBody : FineEmbodiedWaveState
waveThenBody = bodyRegulation (waveTransport rootState)

bodyThenWave : FineEmbodiedWaveState
bodyThenWave = waveTransport (bodyRegulation rootState)

orderedEndpointsDiffer : waveThenBody ≡ bodyThenWave → ⊥
orderedEndpointsDiffer ()

orderedEndpointsSharePublicSurface :
  projectPublic waveThenBody ≡ projectPublic bodyThenWave
orderedEndpointsSharePublicSurface = refl

orderNonfactorability :
  NF.NonFactorabilityWitness
    (λ choice → projectPublic
      (if choice then waveThenBody else bodyThenWave))
    (λ choice → if choice then waveThenBody else bodyThenWave)
orderNonfactorability =
  NF.nonFactorabilityWitness true false refl orderedEndpointsDiffer

publicSurfaceCannotDecodeEmbodiedWaveOrder :
  NF.FactorsThrough
    (λ choice → projectPublic
      (if choice then waveThenBody else bodyThenWave))
    (λ choice → if choice then waveThenBody else bodyThenWave) → ⊥
publicSurfaceCannotDecodeEmbodiedWaveOrder =
  NF.witnessRulesOutEveryFlatFactorisation orderNonfactorability

record EmbodiedWaveHolonomyBoundary : Set where
  constructor embodiedWaveHolonomyBoundary
  field
    updateOrderCanMatterInFineCarrier : Bool
    publicSurfaceCanEraseOrder : Bool
    bodyFirstUniversallyBetter : Bool
    waveFirstUniversallyBetter : Bool
    literalGaugeConnectionConstructed : Bool

canonicalEmbodiedWaveHolonomyBoundary : EmbodiedWaveHolonomyBoundary
canonicalEmbodiedWaveHolonomyBoundary =
  embodiedWaveHolonomyBoundary true true false false false
