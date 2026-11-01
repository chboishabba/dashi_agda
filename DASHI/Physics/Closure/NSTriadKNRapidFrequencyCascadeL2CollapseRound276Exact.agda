module DASHI.Physics.Closure.NSTriadKNRapidFrequencyCascadeL2CollapseRound276Exact where

------------------------------------------------------------------------
-- ROUND276 / HIGH-FREQUENCY ESCAPE -> L2 COLLAPSE ALONG A SEQUENCE
--
-- For an H^(1/2)-almost-periodic solution, concentration near frequency N(t)
-- yields the scaling relation
--
--   ||u(t)||_2^2  ~  N(t)^(-1) ||u(t)||_{H^(1/2)}^2
--
-- up to the low/high frequency tails controlled by compactness.  Therefore
-- N(t_n) -> infinity with a uniformly bounded critical norm implies
-- ||u(t_n)||_2 -> 0.
--
-- IMPORTANT: this alone is NOT a contradiction.  Dissipative Navier--Stokes
-- solutions may have L2 energy tending to zero as t -> infinity.  R277 records
-- the extra dynamical ingredient needed to rule out a bad cascade.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record CascadeL2Collapse {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics
    criticalOrbitAlmostPeriodic : Set ℓ
    criticalNormUniformlyBounded : Set ℓ
    escapingFrequencySequence : Set ℓ
    lowFrequencyTailControlledByCompactness : Set ℓ
    highFrequencyTailControlledByCompactness : Set ℓ
    l2CollapseAlongEscapingSequence : Set ℓ

open CascadeL2Collapse public

round276HighFrequencyEscapeImpliesL2CollapseAlongSequence : Bool
round276HighFrequencyEscapeImpliesL2CollapseAlongSequence = true

round276L2CollapseAloneContradictsNavierStokesEnergy : Bool
round276L2CollapseAloneContradictsNavierStokesEnergy = false

round276CascadeL2CollapseAnalyticInstanceClosed : Bool
round276CascadeL2CollapseAnalyticInstanceClosed = false

round276PackageAClosed : Bool
round276PackageAClosed = false

round276L2CollapseAloneContradictsNavierStokesEnergyIsFalse :
  round276L2CollapseAloneContradictsNavierStokesEnergy ≡ false
round276L2CollapseAloneContradictsNavierStokesEnergyIsFalse = refl
