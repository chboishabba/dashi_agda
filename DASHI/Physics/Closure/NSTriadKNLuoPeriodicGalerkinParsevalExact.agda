module DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinParsevalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Fourier orthogonality and Parseval theorem on a finite periodic
-- abelian group. Repository-original Agda realization; no DOI is assigned.
--
-- Related references:
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Present the concrete (Z/2Z)^3 character and Parseval modules as one
-- Galerkin theorem surface.  No orthogonality, completeness or residual-energy
-- field is accepted from the caller:
--
--   sum_x chi_k(x) chi_l(x) = 8 delta_kl,
--   (1/8) sum_x f(x)^2 = sum_k fhat(k)^2.
--
-- This is an exact finite periodic Galerkin realization. The continuum T^3
-- Haar-integral theorem remains a separate analytic embedding, not a hidden
-- axiom of this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshCharacterOrthogonalityExact as Orthogonality
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshParsevalExact as Parseval

periodicGalerkinCharacterOrthogonality :
  (left right : Orthogonality.Bit3) →
  Orthogonality.eightPointPairSum left right
  ≡ Orthogonality.eight * Orthogonality.modeDelta left right
periodicGalerkinCharacterOrthogonality =
  Orthogonality.eightPointCharacterOrthogonality

periodicGalerkinParseval :
  (signal : Parseval.Signal8) →
  Parseval.fourierL2Squared signal
  ≡ Parseval.physicalL2Squared signal
periodicGalerkinParseval = Parseval.periodicWalshParseval

record ConcretePeriodicGalerkinReceipt : Set where
  constructor concrete-periodic-galerkin-receipt
  field
    signal : Parseval.Signal8
    physicalEnergy fourierEnergy : ℚ
    physicalMeaning :
      physicalEnergy ≡ Parseval.physicalL2Squared signal
    fourierMeaning :
      fourierEnergy ≡ Parseval.fourierL2Squared signal

open ConcretePeriodicGalerkinReceipt public

concretePeriodicGalerkinEnergyEquality :
  (receipt : ConcretePeriodicGalerkinReceipt) →
  fourierEnergy receipt ≡ physicalEnergy receipt
concretePeriodicGalerkinEnergyEquality receipt
  rewrite fourierMeaning receipt
        | physicalMeaning receipt =
  periodicGalerkinParseval (signal receipt)
