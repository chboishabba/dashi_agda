{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedF2HilbertMaxCutExact where

------------------------------------------------------------------------
-- S3a HILBERT MAX-CUT.
--
-- Round88 has already proved the only nontrivial Hilbert inequality needed for
-- a finite localized marked source: weighted Cauchy--Schwarz.  Therefore the
-- selected F^2 lane must not charge an abstract Hilbert-continuity theorem in
-- addition to the physical coefficient estimate.
--
-- For the literal differentiated CMP116 F^2 source, the analytic payment is:
--
--   identify its finite/localized coefficients a_x on the same source;
--   prove sum_x w_x a_x^2 <= C^2 uniformly in cutoff/volume/scale.
--
-- The source-pairing Cauchy estimate is compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; _≤_; _*_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact as Hilbert

record SelectedF2CoefficientEnergyData : Set₁ where
  field
    finiteHilbertData : Hilbert.FiniteMarkedSourceHilbertData

open SelectedF2CoefficientEnergyData public

selectedF2PairingSquaredBound :
  (data : SelectedF2CoefficientEnergyData) →
  L2.square (Hilbert.sourcePairing (finiteHilbertData data))
  ≤
  Hilbert.sourceCoefficientEnergy (finiteHilbertData data)
  * Hilbert.testHilbertEnergy (finiteHilbertData data)
selectedF2PairingSquaredBound data =
  Hilbert.sourcePairingSquaredCauchy (finiteHilbertData data)

selectedF2CoefficientCapPropagates :
  (data : SelectedF2CoefficientEnergyData) →
  Hilbert.sourceCoefficientEnergy (finiteHilbertData data)
  ≤ Hilbert.coefficientEnergyCap (finiteHilbertData data)
selectedF2CoefficientCapPropagates data =
  Hilbert.coefficientEnergyBound (finiteHilbertData data)

abstractIndependentHilbertInequalityRequired : Bool
abstractIndependentHilbertInequalityRequired = false

weightedCauchyCompilerClosed : Bool
weightedCauchyCompilerClosed = true

remainingSelectedF2HilbertSourceWorkIsUniformCoefficientEnergy : Bool
remainingSelectedF2HilbertSourceWorkIsUniformCoefficientEnergy = true

remainingSelectedF2CoefficientSameObjectIdentificationRequired : Bool
remainingSelectedF2CoefficientSameObjectIdentificationRequired = true
