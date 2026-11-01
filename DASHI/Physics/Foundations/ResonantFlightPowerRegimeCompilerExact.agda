module DASHI.Physics.Foundations.ResonantFlightPowerRegimeCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPowerSignExact as Sign
import DASHI.Physics.Foundations.ResonantFlightPhaseCoupledPowerExact as PhasePower

------------------------------------------------------------------------
-- A compact compiler from power sign + modulation mode to an operational
-- phase regime.
------------------------------------------------------------------------

data ModulationMode : Set where
  force stiffness equilibrium none : ModulationMode

record PowerRegimeInput : Set₁ where
  constructor power-regime-input
  field
    Phase : Set
    sign : Phase → Sign.PowerSign
    modulation : Phase → ModulationMode

open PowerRegimeInput public

classifyRegime :
  {Phase : Set} →
  Sign.PowerSign →
  ModulationMode →
  PhasePower.CouplingRegime
classifyRegime Sign.positive force = PhasePower.direct
classifyRegime Sign.positive stiffness = PhasePower.parametric
classifyRegime Sign.positive equilibrium = PhasePower.parametric
classifyRegime Sign.positive none = PhasePower.resonant
classifyRegime Sign.zero force = PhasePower.reversal
classifyRegime Sign.zero stiffness = PhasePower.parametric
classifyRegime Sign.zero equilibrium = PhasePower.parametric
classifyRegime Sign.zero none = PhasePower.reversal
classifyRegime Sign.negative force = PhasePower.regenerative
classifyRegime Sign.negative stiffness = PhasePower.regenerative
classifyRegime Sign.negative equilibrium = PhasePower.regenerative
classifyRegime Sign.negative none = PhasePower.regenerative

record CompiledPowerRegime : Set₁ where
  constructor compiled-power-regime
  field
    Phase : Set
    sign : Phase → Sign.PowerSign
    modulation : Phase → ModulationMode
    regime : Phase → PhasePower.CouplingRegime
    regime-is-classified :
      (φ : Phase) →
      regime φ ≡ classifyRegime (sign φ) (modulation φ)

open CompiledPowerRegime public
