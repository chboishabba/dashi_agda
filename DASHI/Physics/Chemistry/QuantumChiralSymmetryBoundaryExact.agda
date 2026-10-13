module DASHI.Physics.Chemistry.QuantumChiralSymmetryBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as FiniteC3
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as QuantumPhase
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Born
import DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact as ChiralC3

------------------------------------------------------------------------
-- QUANTUM / CHEMISTRY FIREWALL
--
-- The chemistry bridge reuses only the exact C3 involution/conjugation shape.
-- Existing quantum owners make clear that a physical/algorithmic quantum state
-- requires an independent coefficient-amplitude carrier, Fourier action and,
-- for measurement semantics, a Born-weight layer.  A three-valued phase label
-- or a mirror-conjugation intertwiner alone provides none of those objects.
------------------------------------------------------------------------

finiteC3Reading : String
finiteC3Reading =
  "CyclotomicPhaseAmplitudeBoundaryExact explicitly separates finite C3 phase from quantitative amplitude. The chiral bridge consumes only conjugation of phaseOne/zeta/zetaSquared."

quantumAmplitudeReading : String
quantumAmplitudeReading =
  "ShorCyclicPhaseAmplitudeQFTExact represents an actual finite coefficient function over a computational basis and keeps concrete coefficient authority, root-of-unity tables, inversion authority and Born measurement as separate obligations."

bornReading : String
bornReading =
  "ShorFiniteVectorBornWeightsExact is downstream quantum probability machinery. Molecular handedness, enantiomeric excess and asymmetric catalysis are not Born probabilities merely because both domains use phase/conjugation vocabulary."

chiralC3IntertwinerPresent : Bool
chiralC3IntertwinerPresent = true

record QuantumChiralSymmetryBoundary : Set where
  constructor quantumChiralSymmetryBoundary
  field
    sharedConjugationGrammar : Bool
    sharedConjugationGrammarIsTrue : sharedConjugationGrammar ≡ true

    finiteC3PhaseSuppliesQuantumAmplitude : Bool
    finiteC3PhaseSuppliesQuantumAmplitudeIsFalse :
      finiteC3PhaseSuppliesQuantumAmplitude ≡ false

    molecularChiralitySuppliesBornProbability : Bool
    molecularChiralitySuppliesBornProbabilityIsFalse :
      molecularChiralitySuppliesBornProbability ≡ false

    asymmetricAutocatalysisIsQuantumMeasurement : Bool
    asymmetricAutocatalysisIsQuantumMeasurementIsFalse :
      asymmetricAutocatalysisIsQuantumMeasurement ≡ false

    mirrorSymmetryBreakingImpliesQuantumDecoherence : Bool
    mirrorSymmetryBreakingImpliesQuantumDecoherenceIsFalse :
      mirrorSymmetryBreakingImpliesQuantumDecoherence ≡ false

    quantumMechanismForSoaiReactionConstructedHere : Bool
    quantumMechanismForSoaiReactionConstructedHereIsFalse :
      quantumMechanismForSoaiReactionConstructedHere ≡ false

canonicalQuantumChiralSymmetryBoundary : QuantumChiralSymmetryBoundary
canonicalQuantumChiralSymmetryBoundary =
  quantumChiralSymmetryBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
