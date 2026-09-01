module DASHI.Analysis.RiemannG2C3MonsterEquivarianceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Monster369
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed369
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact as Schur

------------------------------------------------------------------------
-- RH G2 / BASE369-MONSTER C3 AUDIT
--
-- The Base369/Monster lane owns exact order-three coordinate rotation on its
-- literal ternary cube and exact conjugation/reflection covariance on its
-- character sectors. Those facts are not imported as facts about the RH
-- three-taper observer.
--
-- A later G2e audit sharpens the priority: after fixed-nuisance determinant
-- compression the literal reflection kernel is common across all three taper
-- coordinates and vector Gram/Schur geometry is no longer the open object.
-- Hence a raw three-channel Fourier decomposition is not highest-alpha merely
-- because three channels exist. A C3 action must control the determinant taper
-- q(u), or a downstream consumer not already factoring through q, to matter.
------------------------------------------------------------------------

monster369OrderThreeRotationOwned : Bool
monster369OrderThreeRotationOwned = true

monster369ReflectionFrequencyCovarianceOwned : Bool
monster369ReflectionFrequencyCovarianceOwned = true

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

g2eVectorGeometryAlreadyCompressed :
  G2e.vectorGramGeometryRemainingAfterCompression
    G2e.canonicalG2eDeterminantTaperKernelBoundary ≡ false
g2eVectorGeometryAlreadyCompressed =
  G2e.vectorGramGeometryRemainingAfterCompressionIsFalse
    G2e.canonicalG2eDeterminantTaperKernelBoundary

------------------------------------------------------------------------
-- Exact theorem-bearing target if a literal action is later found.
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
    c3ControlsDeterminantTaperQ : Set

open RiemannThreeTaperC3Realisation public

------------------------------------------------------------------------
-- Even an inhabited C3 realisation does not prove the signed bound by itself.
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
  "Do not search for a C3 decomposition of the raw three taper coordinates as an end in itself. First ask whether a literal order-three action preserves the nuisance rows and induces a useful invariant/decomposition of q(u)=det3(n1,n2,h(u)). Only such a q-level action can survive the exact G2e scalarization and become theorem-relevant to the current local-zero consumer."
