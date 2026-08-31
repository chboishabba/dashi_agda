module DASHI.Analysis.RiemannG2C3MonsterEquivarianceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Monster369
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed369
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact as Schur

------------------------------------------------------------------------
-- RH G2 / BASE369-MONSTER C3 AUDIT
--
-- The Base369/Monster lane owns exact order-three coordinate rotation on its
-- literal ternary cube and exact conjugation/reflection covariance on its
-- character sectors.  Those facts are not imported as facts about the RH
-- three-taper observer.  They motivate the exact gate below.
------------------------------------------------------------------------

monster369OrderThreeRotationOwned : Bool
monster369OrderThreeRotationOwned = true

monster369ReflectionFrequencyCovarianceOwned : Bool
monster369ReflectionFrequencyCovarianceOwned = true

-- Current RH source surface has three tapers/channels, but no literal order-three
-- action on those actual taper objects has been recovered from the RH owner.
rhThreeTaperChannelsOwned : Bool
rhThreeTaperChannelsOwned = true

rhLiteralC3ActionRecovered : Bool
rhLiteralC3ActionRecovered = false

rhNearVectorC3EquivarianceRecovered : Bool
rhNearVectorC3EquivarianceRecovered = false

rhSchurEliminationC3EquivarianceRecovered : Bool
rhSchurEliminationC3EquivarianceRecovered = false

rhNuisanceSubspaceC3InvariantRecovered : Bool
rhNuisanceSubspaceC3InvariantRecovered = false

rhC3FourierModeEnergyDecompositionRecovered : Bool
rhC3FourierModeEnergyDecompositionRecovered = false

rhLiteralC3ActionRecoveredIsFalse : rhLiteralC3ActionRecovered ≡ false
rhLiteralC3ActionRecoveredIsFalse = refl

------------------------------------------------------------------------
-- Exact theorem-bearing target if the literal action is later found.
------------------------------------------------------------------------

record RiemannThreeTaperC3Realisation : Set₁ where
  field
    Taper : Set
    NearVector : Set
    SchurVector : Set

    taperAction : C3.OrderThreeAction Taper
    nearAction : C3.OrderThreeAction NearVector
    schurAction : C3.OrderThreeAction SchurVector

    nearFromTaper : Taper → NearVector
    schurEliminate : NearVector → SchurVector

    nearEquivariant : C3.EquivariantMap taperAction nearAction nearFromTaper
    schurEquivariant : C3.EquivariantMap nearAction schurAction schurEliminate

    deterministicNuisanceSubspaceInvariant : Set
    fourierModeDecompositionOfSchurEnergy : Set

open RiemannThreeTaperC3Realisation public

------------------------------------------------------------------------
-- BIDI boundary: even an inhabited C3 realisation would reorganise the current
-- finite near-core theorem; it would not prove the signed bound by itself.
------------------------------------------------------------------------

c3RealisationAloneClosesFiniteNearSchurCancellation : Bool
c3RealisationAloneClosesFiniteNearSchurCancellation = false

c3RealisationAloneClosesFiniteNearSchurCancellationIsFalse :
  c3RealisationAloneClosesFiniteNearSchurCancellation ≡ false
c3RealisationAloneClosesFiniteNearSchurCancellationIsFalse = refl

currentFiniteNearSchurStillOpen :
  Schur.finiteNearSchurCancellationClosed
    Schur.canonicalFiniteNearCoreSchurBoundary ≡ false
currentFiniteNearSchurStillOpen =
  Schur.finiteNearSchurCancellationClosedIsFalse
    Schur.canonicalFiniteNearCoreSchurBoundary

currentG2HarmonicLeafStillOpen :
  G2.targetCenteredLocalZeroExponentialSumBoundClosed
    G2.canonicalAristotleG2CurrentCut ≡ false
currentG2HarmonicLeafStillOpen =
  G2.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    G2.canonicalAristotleG2CurrentCut

highestAlphaC3Question : String
highestAlphaC3Question =
  "Does the literal three-taper family admit an order-three action preserving the actual nearOffFinset construction, deterministic nuisance subspace, and Schur elimination? If yes, decompose the post-Schur near energy into exact C3 Fourier sectors; if no, retain the obstruction and do not import Monster/Base369 symmetry by analogy."
