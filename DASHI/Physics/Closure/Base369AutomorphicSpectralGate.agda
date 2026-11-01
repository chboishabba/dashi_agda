module DASHI.Physics.Closure.Base369AutomorphicSpectralGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Stages in the arithmetic-representation-modular assembly.

data SpectralAssemblyStage : Set where
  finiteQuotientStage : SpectralAssemblyStage
  characterStage : SpectralAssemblyStage
  traceSeriesStage : SpectralAssemblyStage
  modularLawStage : SpectralAssemblyStage
  eisensteinStage : SpectralAssemblyStage
  ellipticCurveStage : SpectralAssemblyStage
  jInvariantStage : SpectralAssemblyStage

stageLabel : SpectralAssemblyStage → String
stageLabel finiteQuotientStage = "finite quotient"
stageLabel characterStage = "finite character/irrep"
stageLabel traceSeriesStage = "trace or theta q-series"
stageLabel modularLawStage = "proved modular transformation law"
stageLabel eisensteinStage = "Eisenstein/cusp decomposition"
stageLabel ellipticCurveStage = "constructed genus-one or elliptic spectral curve"
stageLabel jInvariantStage = "j-invariant moduli quotient"

------------------------------------------------------------------------
-- Promotion gates.
--
-- The dependency fields prevent a consumer from promoting Eisenstein or j
-- merely because 3/6/9 phase data exist.

record AutomorphicSpectralGate : Set where
  constructor automorphicSpectralGate
  field
    finiteQuotientChecked : Bool
    finiteCharacterArithmeticChecked : Bool
    traceOrThetaSeriesConstructed : Bool
    modularTransformationLawProved : Bool
    eisensteinDecompositionPromoted : Bool
    ellipticSpectralCurveConstructed : Bool
    jInvariantPromoted : Bool

    eisensteinRequiresModularLaw :
      eisensteinDecompositionPromoted ≡ true →
      modularTransformationLawProved ≡ true

    jRequiresEllipticCurve :
      jInvariantPromoted ≡ true →
      ellipticSpectralCurveConstructed ≡ true

    jRequiresModularOrAlgebraicClassification :
      jInvariantPromoted ≡ true →
      modularTransformationLawProved ≡ true

    boundary : String

open AutomorphicSpectralGate public

base369AutomorphicSpectralGate : AutomorphicSpectralGate
base369AutomorphicSpectralGate =
  automorphicSpectralGate
    true
    true
    false
    false
    false
    false
    false
    (λ ())
    (λ ())
    (λ ())
    "Base369 currently reaches finite cyclic quotients and symbolic character arithmetic. Trace/theta construction, modular transformation laws, Eisenstein decomposition, elliptic spectral curves, and j-invariant classification remain gated and unpromoted."

base369-eisenstein-not-promoted :
  eisensteinDecompositionPromoted base369AutomorphicSpectralGate ≡ false
base369-eisenstein-not-promoted = refl

base369-j-not-promoted :
  jInvariantPromoted base369AutomorphicSpectralGate ≡ false
base369-j-not-promoted = refl
