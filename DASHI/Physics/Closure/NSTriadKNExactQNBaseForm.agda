module DASHI.Physics.Closure.NSTriadKNExactQNBaseForm where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNExactGramBaseFormBridge as ExactGramBridge
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Active exact qBase term on the current canonical NS carrier.
--
-- This does not prove the Gram/Rayleigh coercive lower bound. It only fixes
-- the base quadratic form used downstream so that Blocker 2 no longer carries
-- an extra free `Carrier -> Nat` slot.

exactKNAQBase :
  {N : Nat} →
  ResidueNorm.ResidueEnergyCarrier N → Nat
exactKNAQBase x =
  ResidueNorm.residueEnergy x

canonicalExactKNABaseQuadraticFormIdentificationTarget :
  {N : Nat} →
  ExactGramBridge.ExactKNABaseQuadraticFormIdentificationTarget
    (ResidueNorm.ResidueEnergyCarrier N)
canonicalExactKNABaseQuadraticFormIdentificationTarget {N} =
  ExactGramBridge.toExactKNABaseQuadraticFormIdentificationTarget
    ExactGramBridge.canonicalExactKNAPositiveSubspaceCarrierTarget
    exactKNAQBase
