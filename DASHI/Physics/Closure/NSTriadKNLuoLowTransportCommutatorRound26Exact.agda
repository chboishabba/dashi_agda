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
--
-- This module also connects directly to the stronger pre-existing periodic
-- far-low stack:
--
-- * NSPeriodicFarLowExactCommutatorIdentity proves the tested shell identity;
-- * NSPeriodicFarLowMultiplierDifferenceKernel owns the signed multiplier
--   difference and keeps it distinct from its absolute majorant;
-- * NSPeriodicFarLowMultiplierDifferenceBound proves the pointwise mean-value
--   reduction while leaving cutoff-uniform operator control conditional.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (machineChecked)

import DASHI.Physics.Closure.NSPeriodicFarLowEnergyPairingCancellation as Transport
import DASHI.Physics.Closure.NSPeriodicFarLowExactCommutatorIdentity as Exact
import DASHI.Physics.Closure.NSPeriodicFarLowMultiplierDifferenceKernel as Difference
import DASHI.Physics.Closure.NSPeriodicFarLowMultiplierDifferenceBound as DifferenceBound
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

------------------------------------------------------------------------
-- Existing physical shell identity, now named at the Round 26 seam.
------------------------------------------------------------------------

exactProjectedLowTransportCommutator :
  ∀ {ℓ} {Index Field Scalar : Set ℓ} →
  (S : Exact.ShellCommutatorStructure Index Field Scalar) →
  ∀ j a v → Transport.DivergenceFree (Exact.energy S) a →
  Transport.pairing (Exact.energy S)
    (Exact.shell S j (Transport.transport (Exact.energy S) a v))
    (Exact.shell S j v)
  ≡
  Transport.pairing (Exact.energy S)
    (Exact.commutator S j a v)
    (Exact.shell S j v)
exactProjectedLowTransportCommutator =
  Exact.exactFarLowCommutatorEnergyIdentity

------------------------------------------------------------------------
-- Existing signed multiplier-difference kernel, retained before absolute
-- values.  This is the Fourier counterpart of the finite increment identity.
------------------------------------------------------------------------

signedCommutatorIsLiteralMultiplierDifference :
  ∀ {ℓ} {Shell Mode Scalar : Set ℓ}
    {A : Difference.KernelScalarAlgebra Scalar} →
  (K : Difference.FarLowFourierKernelData Shell Mode Scalar A) →
  ∀ j k p q →
  Difference.commutatorKernel K j k p q
  ≡ Difference.differenceKernel K j k p q
signedCommutatorIsLiteralMultiplierDifference =
  Difference.commutatorIsLiteralDifference

finiteLowTransportCommutatorIsIncrement :
  (cells : List Kernel.FiniteKernelTransportCell) →
  Kernel.sumCommutatorCells cells
  ≡ Kernel.sumIncrementCells cells
finiteLowTransportCommutatorIsIncrement =
  Kernel.finiteKernelCommutatorIdentity

record LowTransportCommutatorCertificate
    {ℓ : Level}
    (Field Scalar : Set ℓ) : Set (lsuc ℓ) where
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
-- The existing pointwise mean-value reduction is machine checked, but its
-- concrete smooth profile and cutoff-uniform row/column or signed operator
-- bounds remain conditional.  The final analytic theorem is therefore still:
--
--   sum_q 2^{-q} |<commutator_q, omega_q>|
--     <= eta_Com D + C X + R,
--
-- with cutoff-independent constants.
------------------------------------------------------------------------

pointwiseMultiplierDifferenceReductionChecked :
  DifferenceBound.farLowMultiplierDifferenceReductionLevel
  ≡ machineChecked
pointwiseMultiplierDifferenceReductionChecked = refl

lowTransportSupportAndCancellationClosed : DerivativePlacementClass
lowTransportSupportAndCancellationClosed = LowAdvectsHigh
