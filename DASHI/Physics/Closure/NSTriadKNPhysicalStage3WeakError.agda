module DASHI.Physics.Closure.NSTriadKNPhysicalStage3WeakError where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierShellData as Fourier
import DASHI.Physics.Closure.NSTriadKNExactRetainedPairIncidences as Incidence
import DASHI.Physics.Closure.NSTriadKNPhysicalGramOperatorAssembly as Gram
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as PhysicalSector
import DASHI.Physics.Closure.NSTriadKNStage3NegativeTransferContrast as Contrast

------------------------------------------------------------------------
-- Physical Stage-3 negative-transfer Gram surrogate.
--
-- This is the canonical auxiliary object for the physical Fourier/Gram lane.
-- It is intentionally distinct from the legacy Nat-valued diagnostic
-- `actualWeakQuadraticForm`, and it is also not yet identified with the full
-- weighted Fourier NS error.  A full error bound must include a separately
-- controlled transfer-flux remainder: a positive orbit interaction has
-- m^- = 0 while its weighted modal-transfer contrast can be nonzero.
-- Moreover, the present m^abs is the absolute transfer into one distinguished
-- output mode; it need not control the full three-mode transfer variation.
-- Thus neither current Gram coefficient can be used as a Young parameter for
-- the full weighted-energy term without a new modal-transfer/dissipation
-- estimate.
--
-- The concrete pair-incidence instance has one edge for each oriented pair
-- slot of a retained triad, with coefficient m^-_tau(u) / 3 and vector
-- e_source - e_target.  Consequently this definition is exactly
--
--   sum_tau m^-_tau(u) / 3
--     [ (z_p - z_q)^2 + (z_p - z_r)^2 + (z_q - z_r)^2 ].
------------------------------------------------------------------------

physicalStage3WeakError :
  {S : Exact.ExactScalarOperations} →
  {H : Gram.FiniteShellInnerProductSpace S} {A : Set} →
  Contrast.NegativeTransferContrastData {A = A} H →
  Contrast.ShellObservable H →
  Exact.ExactScalarOperations.Carrier S
physicalStage3WeakError = Contrast.negativeTransferContrast

physicalStage3WeakErrorGramIdentity :
  {S : Exact.ExactScalarOperations} →
  {H : Gram.FiniteShellInnerProductSpace S} {A : Set} →
  (assembly : Contrast.NegativeTransferContrastData {A = A} H) →
  (z : Contrast.ShellObservable H) →
  physicalStage3WeakError assembly z ≡
  Gram.inner H z (Contrast.physicalLNeg assembly z)
physicalStage3WeakErrorGramIdentity =
  Contrast.negativeTransferContrastGramIdentity

physicalStage3WeakErrorFromFourierData :
  (S : Scalar.ExactOrderedScalar) →
  (C : Fourier.ComplexFourierInterface S) →
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (H : Gram.FiniteShellInnerProductSpace (Scalar.exactScalarOperations S)) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (pairIncidenceVector : Incidence.PairIncidence → Gram.Vector H) →
  Contrast.ShellObservable H → Scalar.Scalar S
physicalStage3WeakErrorFromFourierData S C N R sector H u vector =
  physicalStage3WeakError
    (Contrast.physicalCutoffNegativeTransferContrastFromFourierData
      S C N R sector H u vector)

------------------------------------------------------------------------
-- Scalar-valued replacement for the diagnostic weak-quadratic interface.
--
-- N and R label the output shell and finite Fourier cutoff.  The present
-- generic Gram construction stores the state-dependent coefficients in
-- `assembly`; a concrete Fourier construction must prove that they are the
-- m^-_tau(u)/3 coefficients for this particular N, R, and shell state.
------------------------------------------------------------------------

record PhysicalStage3WeakQuadraticControl
    {S : Exact.ExactScalarOperations} {A : Set}
    (N R : Nat)
    (H : Gram.FiniteShellInnerProductSpace S)
    (assembly : Contrast.NegativeTransferContrastData {A = A} H) : Set₁ where
  constructor mkPhysicalStage3WeakQuadraticControl
  field
    _≤q_ : Exact.ExactScalarOperations.Carrier S →
           Exact.ExactScalarOperations.Carrier S → Set

    -- Kept as a field so later coercivity/q-gap machinery can consume a
    -- named error functional, while the equality below prevents it from
    -- becoming a new opaque Stage-3 model.
    qError : Contrast.ShellObservable H →
             Exact.ExactScalarOperations.Carrier S

    qErrorIsNegativeTransferContrast :
      (z : Contrast.ShellObservable H) →
      qError z ≡ physicalStage3WeakError assembly z

    operatorQuadraticIdentity :
      (z : Contrast.ShellObservable H) →
      qError z ≡ Gram.inner H z (Contrast.physicalLNeg assembly z)

open PhysicalStage3WeakQuadraticControl public

canonicalPhysicalStage3WeakQuadraticControl :
  {S : Exact.ExactScalarOperations} {A : Set} →
  (N R : Nat) →
  (H : Gram.FiniteShellInnerProductSpace S) →
  (assembly : Contrast.NegativeTransferContrastData {A = A} H) →
  (_≤q_ : Exact.ExactScalarOperations.Carrier S →
          Exact.ExactScalarOperations.Carrier S → Set) →
  PhysicalStage3WeakQuadraticControl N R H assembly
canonicalPhysicalStage3WeakQuadraticControl N R H assembly _≤q_ =
  mkPhysicalStage3WeakQuadraticControl
    _≤q_
    (physicalStage3WeakError assembly)
    (λ z → refl)
    (physicalStage3WeakErrorGramIdentity assembly)

canonicalPhysicalStage3WeakQuadraticControlFromFourierData :
  (S : Scalar.ExactOrderedScalar) →
  (C : Fourier.ComplexFourierInterface S) →
  (N R : Nat) →
  (sector : PhysicalSector.ExactOutputRetainedSectorLaw N R) →
  {interaction : Fourier.PhysicalTriadInteractionLaw S C N} →
  (H : Gram.FiniteShellInnerProductSpace (Scalar.exactScalarOperations S)) →
  (u : Fourier.AdmissibleFourierShellData S C N interaction) →
  (pairIncidenceVector : Incidence.PairIncidence → Gram.Vector H) →
  (_≤q_ : Scalar.Scalar S → Scalar.Scalar S → Set) →
  PhysicalStage3WeakQuadraticControl N R H
    (Contrast.physicalCutoffNegativeTransferContrastFromFourierData
      S C N R sector H u pairIncidenceVector)
canonicalPhysicalStage3WeakQuadraticControlFromFourierData
  S C N R sector H u vector _≤q_ =
  canonicalPhysicalStage3WeakQuadraticControl N R H
    (Contrast.physicalCutoffNegativeTransferContrastFromFourierData
      S C N R sector H u vector)
    _≤q_

------------------------------------------------------------------------
-- The remaining PDE theorem.
--
-- This surface makes the missing bridge precise: it is an energy estimate
-- derived from the finite Fourier Navier--Stokes equations, not a theorem
-- inherited from the Nat-valued diagnostic pair-incidence witness.  The
-- eventual bridge must be flux-inclusive rather than asserting that the
-- full weak error is bounded by the negative Gram surrogate alone.
------------------------------------------------------------------------

record PhysicalStage3EnergyEstimate
    {S : Exact.ExactScalarOperations} {A : Set}
    (N R : Nat)
    (H : Gram.FiniteShellInnerProductSpace S)
    (assembly : Contrast.NegativeTransferContrastData {A = A} H)
    (control : PhysicalStage3WeakQuadraticControl N R H assembly) : Set₁ where
  constructor mkPhysicalStage3EnergyEstimate
  field
    energy : Contrast.ShellObservable H →
             Exact.ExactScalarOperations.Carrier S
    timeDerivative : Contrast.ShellObservable H →
                     Exact.ExactScalarOperations.Carrier S
    dissipation : Contrast.ShellObservable H →
                  Exact.ExactScalarOperations.Carrier S
    weakError : Contrast.ShellObservable H →
                Exact.ExactScalarOperations.Carrier S

    energyInequality :
      (z : Contrast.ShellObservable H) →
      _≤q_ control
        (Exact.ExactScalarOperations._+_ S
          (timeDerivative z) (dissipation z))
        (weakError z)

    weakErrorControlledByNegativeTransferContrast :
      (z : Contrast.ShellObservable H) →
      _≤q_ control (weakError z) (qError control z)

open PhysicalStage3EnergyEstimate public

-- No Fourier NS energy/error derivation has yet inhabited this record.
-- In particular, this diagnostic negative-transfer Gram form is not the
-- controller of the physical weighted Fourier error: that error is linear in
-- multiplier contrasts.  The canonical physical bridge now lives in
-- `NSTriadKNPhysicalEdgeTransferOperator` plus a coercive weighted Young
-- estimate and a strictly absorbable transfer-flux remainder.
physicalStage3EnergyEstimateClosed : Bool
physicalStage3EnergyEstimateClosed = false

-- The scalar physical route has not been connected to the legacy Nat q-gap
-- interface.  That interface uses truncated natural subtraction and cannot
-- faithfully represent this ordered-scalar functional without a separate
-- scalar coercivity and scale-compatibility theorem.
physicalScalarQGapCompatibilityClosed : Bool
physicalScalarQGapCompatibilityClosed = false
