module DASHI.Physics.Closure.NSTriadKNLuoHarmonicCrossPollinationRound17Validation where

------------------------------------------------------------------------
-- Cumulative validation root.
--
-- Imports the complete physical-carrier Round Sixteen and checks the shared
-- ring-scale, filtered-limit, separating-probe and local-permutation modules,
-- together with their NS adapters.  No centered continuum kernel theorem,
-- physical Sobolev projection error, Yu tail, F3 directional estimate or
-- global regularity result is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalCarrierRound16Validation
import DASHI.Physics.Common.FiniteRingScaleDualityExact
import DASHI.Physics.Common.ScaledFilteredEstimateExact
import DASHI.Physics.Common.SeparatingProbeFamilyExact
import DASHI.Physics.Common.FiniteWreathRefinementExact
import DASHI.Physics.Closure.NSTriadKNLuoRelativeScaleProbeCrossPollinationExact
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinScaledFiltrationCrossPollinationExact

round17HarmonicCrossPollinationRoot : Set
round17HarmonicCrossPollinationRoot = ⊤

round17HarmonicCrossPollinationRootInhabited :
  round17HarmonicCrossPollinationRoot
round17HarmonicCrossPollinationRootInhabited = tt

round17HarmonicCrossPollinationRootStable :
  round17HarmonicCrossPollinationRoot ≡ ⊤
round17HarmonicCrossPollinationRootStable = refl
