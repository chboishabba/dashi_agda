module DASHI.Physics.Closure.NSTriadKNLuoLowTransportCommutatorRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Naming is fixed by derivative placement: a low velocity advects the tested
-- high vorticity.  Its principal self-tested transport term cancels exactly;
-- the surviving finite-filter contribution is the kernel commutator, which is
-- exactly the advecting-field increment sum proved in Round 26.  No LH/HL
-- mnemonic is used at this seam.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSPeriodicFarLowEnergyPairingCancellation as Transport
import DASHI.Physics.Closure.NSTriadKNLuoFiniteKernelCommutatorRound26Exact as Kernel

data DerivativePlacementClass : Set where
  LowAdvectsHigh : DerivativePlacementClass
  HighActsOnLow : DerivativePlacementClass
  ComparableInputs : DerivativePlacementClass
  HighHighInputs : DerivativePlacementClass

lowTransportExactCancellation :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (S : Transport.PeriodicTransportEnergyStructure Field Scalar) →
  ∀ a → (P : Transport.OfficialSelfTestPairing Field) →
  Transport.DivergenceFree S a →
  Transport.pairing S
    (Transport.transport S a (Transport.advectedShell P))
    (Transport.testedShell P)
  ≡ Transport.scalarZero S
lowTransportExactCancellation =
  Transport.officialPrincipalTermCancels

finiteLowTransportCommutatorIsIncrement :
  (cells : List Kernel.FiniteKernelTransportCell) →
  Kernel.sumCommutatorCells cells
  ≡ Kernel.sumIncrementCells cells
finiteLowTransportCommutatorIsIncrement =
  Kernel.finiteKernelCommutatorIdentity

record LowTransportCommutatorCertificate
    {ℓ : Level}
    (Field Scalar : Set ℓ) : Set ℓ where
  constructor low-transport-commutator-certificate
  field
    transportStructure :
      Transport.PeriodicTransportEnergyStructure Field Scalar
    lowVelocity : Field
    shellPairing : Transport.OfficialSelfTestPairing Field
    lowVelocityDivergenceFree :
      Transport.DivergenceFree transportStructure lowVelocity
    finiteKernelCells : List Kernel.FiniteKernelTransportCell

open LowTransportCommutatorCertificate public

principalLowTransportCancels :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (certificate : LowTransportCommutatorCertificate Field Scalar) →
  Transport.pairing (transportStructure certificate)
    (Transport.transport (transportStructure certificate)
      (lowVelocity certificate)
      (Transport.advectedShell (shellPairing certificate)))
    (Transport.testedShell (shellPairing certificate))
  ≡ Transport.scalarZero (transportStructure certificate)
principalLowTransportCancels certificate =
  lowTransportExactCancellation
    (transportStructure certificate)
    (lowVelocity certificate)
    (shellPairing certificate)
    (lowVelocityDivergenceFree certificate)

survivingFiniteTermIsIncrementCommutator :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (certificate : LowTransportCommutatorCertificate Field Scalar) →
  Kernel.sumCommutatorCells (finiteKernelCells certificate)
  ≡ Kernel.sumIncrementCells (finiteKernelCells certificate)
survivingFiniteTermIsIncrementCommutator certificate =
  finiteLowTransportCommutatorIsIncrement
    (finiteKernelCells certificate)

------------------------------------------------------------------------
-- The remaining analytic theorem is quantitative, not algebraic:
--
--   sum_q 2^{-q} |<commutator_q, omega_q>|
--     <= eta_Com D + C X + R,
--
-- with cutoff-independent constants.  This module does not mark that estimate
-- as proved.
------------------------------------------------------------------------

lowTransportSupportAndCancellationClosed : DerivativePlacementClass
lowTransportSupportAndCancellationClosed = LowAdvectsHigh
