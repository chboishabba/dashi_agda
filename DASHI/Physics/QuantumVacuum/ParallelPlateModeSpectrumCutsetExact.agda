module DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- PHYSICAL PARALLEL-PLATE MODE-SPECTRUM CUTSET
--
-- This module moves the Casimir lane from a toy finite mode witness to the
-- exact physical obligations needed for the ideal conducting-plate result.
-- It does not fabricate the continuum/renormalisation theorem.
--
-- For a plate separation d, a physical mode has transverse momentum k_perp,
-- longitudinal integer n, and polarization.  Its frequency must satisfy
--
--   omega = c sqrt(k_perp^2 + (n pi / d)^2).
--
-- A regulated mode sum is then compared with a reference vacuum and only the
-- renormalised difference may be welded to the existing Casimir kernel.
------------------------------------------------------------------------

data Polarisation : Set where
  TE TM : Polarisation

record ParallelPlateModeIndex (Transverse : Set) : Set where
  constructor parallelPlateMode
  field
    transverse : Transverse
    longitudinal : Nat
    polarisation : Polarisation

open ParallelPlateModeIndex public

record ParallelPlateSpectralModel
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    Transverse : Set
    Mode : Set

    modeIndex : Mode → ParallelPlateModeIndex Transverse

    transverseSquared : Transverse → Casimir.Scalar kernel
    square root : Casimir.Scalar kernel → Casimir.Scalar kernel
    divide : Casimir.Scalar kernel → Casimir.Scalar kernel → Casimir.Scalar kernel

    frequency : Q.Length → Mode → Casimir.Scalar kernel
    admissible : Q.Length → Mode → Set

    frequencyLaw :
      (d : Q.Length) →
      (m : Mode) →
      admissible d m →
      frequency d m ≡
        Casimir.lightSpeed kernel Casimir.*
        root
          (transverseSquared (transverse (modeIndex m)) Casimir.+
           square
             (divide
               (Casimir.fromNat kernel (longitudinal (modeIndex m)) Casimir.*
                Casimir.pi kernel)
               (Casimir.lengthValue kernel d)))

    spectralReading : String

open ParallelPlateSpectralModel public

------------------------------------------------------------------------
-- Regulated finite approximants.
--
-- The regulator chooses finite mode carriers on both the plate and reference
-- sides.  The sum law is explicit and modewise uses (1/2) hbar omega.
------------------------------------------------------------------------

record ParallelPlateRegulator
    {kernel : Casimir.CasimirScalarModel}
    (spectrum : ParallelPlateSpectralModel kernel) : Set₁ where
  field
    Cutoff : Set
    cutoff : Cutoff

    plateModes : Q.Length → Cutoff → List (Mode spectrum)
    referenceModes : Q.Length → Cutoff → List (Mode spectrum)

    sumScalar : List (Casimir.Scalar kernel) → Casimir.Scalar kernel
    mapScalar :
      (Mode spectrum → Casimir.Scalar kernel) →
      List (Mode spectrum) →
      List (Casimir.Scalar kernel)

    zeroPointContribution :
      Q.Length → Mode spectrum → Casimir.Scalar kernel

    zeroPointLaw :
      (d : Q.Length) → (m : Mode spectrum) →
      zeroPointContribution d m ≡
        (Casimir.hbar kernel Casimir.* frequency spectrum d m) Casimir.*
        divide spectrum (Casimir.one kernel) (Casimir.fromNat kernel 2)

    regulatedPlateEnergy : Q.Length → Cutoff → Casimir.Scalar kernel
    regulatedReferenceEnergy : Q.Length → Cutoff → Casimir.Scalar kernel

    plateSumLaw :
      (d : Q.Length) → (Λ : Cutoff) →
      regulatedPlateEnergy d Λ ≡
        sumScalar
          (mapScalar
            (zeroPointContribution d)
            (plateModes d Λ))

    referenceSumLaw :
      (d : Q.Length) → (Λ : Cutoff) →
      regulatedReferenceEnergy d Λ ≡
        sumScalar
          (mapScalar
            (zeroPointContribution d)
            (referenceModes d Λ))

    regulatorReading : String

open ParallelPlateRegulator public

------------------------------------------------------------------------
-- Renormalised continuum receipt: THIS is the hard analytic leaf.
--
-- The receipt must simultaneously identify the physical spectrum, control the
-- regulator/removal limit, subtract the reference vacuum on the same scalar
-- carrier, and prove agreement with -pi^2 hbar c/(720 d^3).
------------------------------------------------------------------------

record ParallelPlateRenormalisedEvaluation
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    spectrum : ParallelPlateSpectralModel kernel
    regulator : ParallelPlateRegulator spectrum

    RenormalisedDifference : Set
    renormalisedDifference : Q.Length → RenormalisedDifference

    regulatorRemovalAndReferenceSubtraction : Set
    finiteApproximantsConvergeToRenormalisedDifference :
      regulatorRemovalAndReferenceSubtraction

    sameScalarObservable :
      Q.Length → RenormalisedDifference → Casimir.Scalar kernel

    energyPerAreaWeld :
      (d : Q.Length) →
      sameScalarObservable d (renormalisedDifference d) ≡
      Casimir.energyPerArea kernel d

    derivativeCarrier : Set
    boundaryDerivativeProducesPressure : derivativeCarrier

    pressureWeld :
      (d : Q.Length) → Set

    evaluationReading : String

open ParallelPlateRenormalisedEvaluation public

------------------------------------------------------------------------
-- Once the analytic receipt exists, the existing kernel formula is compiler
-- output on the same object.  No further physical mode-sum theorem is needed.
------------------------------------------------------------------------

renormalisedDifferenceHasCasimirEnergyLaw :
  (kernel : Casimir.CasimirScalarModel) →
  (evaluation : ParallelPlateRenormalisedEvaluation kernel) →
  (d : Q.Length) →
  sameScalarObservable evaluation d (renormalisedDifference evaluation d) ≡
  Casimir.negate kernel
    (((Casimir.pi kernel Casimir.* Casimir.pi kernel) Casimir.*
      (Casimir.hbar kernel Casimir.* Casimir.lightSpeed kernel)) Casimir.*
     Casimir.inverse kernel
       (Casimir.fromNat kernel 720 Casimir.*
        Casimir.power3 kernel (Casimir.lengthValue kernel d)))
renormalisedDifferenceHasCasimirEnergyLaw kernel evaluation d =
  trans
    (energyPerAreaWeld evaluation d)
    (Casimir.energyLaw kernel d)

------------------------------------------------------------------------
-- Machine-readable cutset.  Everything except the continuum/renormalised
-- evaluation is now architecture or existing-kernel output.
------------------------------------------------------------------------

record ParallelPlateCutsetStatus : Set where
  field
    oscillatorZeroPointFormulaOwned : Bool
    boundaryModeNonFactorabilityOwned : Bool
    rationalHalfScaleOwned : Bool
    physicalModeSpectrumInterfaceOwned : Bool
    regulatorInterfaceOwned : Bool
    renormalisedContinuumEvaluationClosed : Bool
    casimirKernelAlreadyOwned : Bool
    resetCycleClosedBySpectralEvaluation : Bool

    oscillatorZeroPointFormulaOwnedIsTrue :
      oscillatorZeroPointFormulaOwned ≡ true
    boundaryModeNonFactorabilityOwnedIsTrue :
      boundaryModeNonFactorabilityOwned ≡ true
    rationalHalfScaleOwnedIsTrue : rationalHalfScaleOwned ≡ true
    physicalModeSpectrumInterfaceOwnedIsTrue :
      physicalModeSpectrumInterfaceOwned ≡ true
    regulatorInterfaceOwnedIsTrue : regulatorInterfaceOwned ≡ true
    renormalisedContinuumEvaluationClosedIsFalse :
      renormalisedContinuumEvaluationClosed ≡ false
    casimirKernelAlreadyOwnedIsTrue : casimirKernelAlreadyOwned ≡ true
    resetCycleClosedBySpectralEvaluationIsFalse :
      resetCycleClosedBySpectralEvaluation ≡ false

open ParallelPlateCutsetStatus public

canonicalParallelPlateCutsetStatus : ParallelPlateCutsetStatus
canonicalParallelPlateCutsetStatus =
  record
    { oscillatorZeroPointFormulaOwned = true
    ; boundaryModeNonFactorabilityOwned = true
    ; rationalHalfScaleOwned = true
    ; physicalModeSpectrumInterfaceOwned = true
    ; regulatorInterfaceOwned = true
    ; renormalisedContinuumEvaluationClosed = false
    ; casimirKernelAlreadyOwned = true
    ; resetCycleClosedBySpectralEvaluation = false
    ; oscillatorZeroPointFormulaOwnedIsTrue = refl
    ; boundaryModeNonFactorabilityOwnedIsTrue = refl
    ; rationalHalfScaleOwnedIsTrue = refl
    ; physicalModeSpectrumInterfaceOwnedIsTrue = refl
    ; regulatorInterfaceOwnedIsTrue = refl
    ; renormalisedContinuumEvaluationClosedIsFalse = refl
    ; casimirKernelAlreadyOwnedIsTrue = refl
    ; resetCycleClosedBySpectralEvaluationIsFalse = refl
    }
