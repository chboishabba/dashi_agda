module DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- PHYSICAL PARALLEL-PLATE MODE-SPECTRUM CUTSET
--
-- For ideal conducting plates, a mode is indexed by transverse momentum,
-- longitudinal integer n, and polarization, with
--
--   omega = c sqrt(k_perp^2 + (n pi / d)^2).
--
-- The regulated plate/reference sums are kept distinct from the renormalised
-- observable.  The only genuinely open analytic leaf is regulator removal +
-- reference subtraction + continuum evaluation on the physical spectrum.
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
        Casimir._*_ kernel
          (Casimir.lightSpeed kernel)
          (root
            (Casimir._+_ kernel
              (transverseSquared (transverse (modeIndex m)))
              (square
                (divide
                  (Casimir._*_ kernel
                    (Casimir.fromNat kernel (longitudinal (modeIndex m)))
                    (Casimir.pi kernel))
                  (Casimir.lengthValue kernel d)))))

    spectralReading : String

open ParallelPlateSpectralModel public

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
        Casimir._*_ kernel
          (Casimir._*_ kernel
            (Casimir.hbar kernel)
            (frequency spectrum d m))
          (divide spectrum
            (Casimir.one kernel)
            (Casimir.fromNat kernel 2))

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
-- HARD ANALYTIC LEAF.
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
    pressureWeld : (d : Q.Length) → Set

    evaluationReading : String

open ParallelPlateRenormalisedEvaluation public

renormalisedDifferenceHasCasimirEnergyLaw :
  (kernel : Casimir.CasimirScalarModel) →
  (evaluation : ParallelPlateRenormalisedEvaluation kernel) →
  (d : Q.Length) →
  sameScalarObservable evaluation d (renormalisedDifference evaluation d) ≡
  Casimir.negate kernel
    (Casimir._*_ kernel
      (Casimir._*_ kernel
        (Casimir._*_ kernel
          (Casimir.pi kernel)
          (Casimir.pi kernel))
        (Casimir._*_ kernel
          (Casimir.hbar kernel)
          (Casimir.lightSpeed kernel)))
      (Casimir.inverse kernel
        (Casimir._*_ kernel
          (Casimir.fromNat kernel 720)
          (Casimir.power3 kernel (Casimir.lengthValue kernel d)))))
renormalisedDifferenceHasCasimirEnergyLaw kernel evaluation d =
  trans
    (energyPerAreaWeld evaluation d)
    (Casimir.energyLaw kernel d)

------------------------------------------------------------------------
-- Exact cutset status.
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

    oscillatorZeroPointFormulaOwnedIsTrue : oscillatorZeroPointFormulaOwned ≡ true
    boundaryModeNonFactorabilityOwnedIsTrue : boundaryModeNonFactorabilityOwned ≡ true
    rationalHalfScaleOwnedIsTrue : rationalHalfScaleOwned ≡ true
    physicalModeSpectrumInterfaceOwnedIsTrue : physicalModeSpectrumInterfaceOwned ≡ true
    regulatorInterfaceOwnedIsTrue : regulatorInterfaceOwned ≡ true
    renormalisedContinuumEvaluationClosedIsFalse : renormalisedContinuumEvaluationClosed ≡ false
    casimirKernelAlreadyOwnedIsTrue : casimirKernelAlreadyOwned ≡ true
    resetCycleClosedBySpectralEvaluationIsFalse : resetCycleClosedBySpectralEvaluation ≡ false

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
