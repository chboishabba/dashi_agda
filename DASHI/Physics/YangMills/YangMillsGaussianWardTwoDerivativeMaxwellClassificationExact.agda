module DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact where

------------------------------------------------------------------------
-- ROUND77: LOCAL TWO-DERIVATIVE WARD KERNEL -> MAXWELL, EXACTLY
--
-- PRIMARY / CALIBRATION SOURCES
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems. No DOI assigned.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed., Springer,
-- 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- E. Huguet and J. Renaud,
-- "Two-point function for the Maxwell field in flat Robertson-Walker
-- spacetimes", Physical Review D 88 (2013), 124018.
-- DOI: 10.1103/PhysRevD.88.124018.
--
-- AUTHORITY BOUNDARY
--
-- The sources calibrate the standard Gaussian/free-field and Maxwell
-- reconstruction statements.  The finite coefficient classification below is
-- a DASHI theorem.  It does NOT assume "Gaussian => massless".  Instead it
-- uses the exact local/O(4)-covariant two-derivative tensor ansatz and the Ward
-- identity at two nonzero momentum squares.
--
-- If
--
--   K_{mu nu}(p)
--     = (m^2 + Z p^2) delta_{mu nu} + Y p_mu p_nu
--
-- and p_mu K_{mu nu}=0 for all nonzero p, then the scalar Ward coefficient
--
--   m^2 + (Z+Y) p^2
--
-- vanishes.  Evaluating at two distinct nonzero p^2 values forces
--
--   m^2 = 0,    Z+Y = 0.
--
-- Standard kinetic normalization Z=1 then forces Y=-1, hence the kernel is
-- exactly the Maxwell transverse quadratic kernel
--
--   p^2 delta_{mu nu} - p_mu p_nu.
--
-- This is the finite algebraic heart of the Round76 Gaussian/Ward shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-facing coefficient package.
--
-- `wardAtOne` and `wardAtTwo` are not arbitrary scalar receipts: they are the
-- two evaluations of one polynomial coefficient dictated by the local
-- two-derivative O(4)-covariant tensor ansatz.  A physical continuum theorem
-- should construct them by specializing the SAME exact Ward identity.
------------------------------------------------------------------------

record LocalTwoDerivativeWardKernel : Set where
  field
    massSquared waveCoefficient longitudinalCoefficient : ℚ

    wardAtOne :
      massSquared + (waveCoefficient + longitudinalCoefficient) * 1ℚ
      ≡ 0ℚ

    wardAtTwo :
      massSquared
        + (waveCoefficient + longitudinalCoefficient) * (+ 2 / 1)
      ≡ 0ℚ

    -- Standard normalization of the local Yang--Mills quadratic kinetic term.
    waveNormalized : waveCoefficient ≡ 1ℚ

open LocalTwoDerivativeWardKernel public

wardSlopeZero :
  (kernel : LocalTwoDerivativeWardKernel) →
  waveCoefficient kernel + longitudinalCoefficient kernel ≡ 0ℚ
wardSlopeZero kernel =
  let
    m = massSquared kernel
    s = waveCoefficient kernel + longitudinalCoefficient kernel

    differenceEquality :
      (m + s * (+ 2 / 1)) - (m + s * 1ℚ)
      ≡ 0ℚ - 0ℚ
    differenceEquality =
      cong₂ _-_ (wardAtTwo kernel) (wardAtOne kernel)

    leftNormalForm :
      (m + s * (+ 2 / 1)) - (m + s * 1ℚ) ≡ s
    leftNormalForm = ℚRing.solve-∀ m s

    rightNormalForm : 0ℚ - 0ℚ ≡ 0ℚ
    rightNormalForm = ℚRing.solve []
  in
  trans (sym leftNormalForm)
    (trans differenceEquality rightNormalForm)

wardMassTermZero :
  (kernel : LocalTwoDerivativeWardKernel) →
  massSquared kernel ≡ 0ℚ
wardMassTermZero kernel =
  let
    m = massSquared kernel
    s = waveCoefficient kernel + longitudinalCoefficient kernel

    differenceEquality :
      (m + s * 1ℚ) - s ≡ 0ℚ - 0ℚ
    differenceEquality =
      cong₂ _-_ (wardAtOne kernel) (wardSlopeZero kernel)

    leftNormalForm : (m + s * 1ℚ) - s ≡ m
    leftNormalForm = ℚRing.solve-∀ m s

    rightNormalForm : 0ℚ - 0ℚ ≡ 0ℚ
    rightNormalForm = ℚRing.solve []
  in
  trans (sym leftNormalForm)
    (trans differenceEquality rightNormalForm)

longitudinalIsMinusOne :
  (kernel : LocalTwoDerivativeWardKernel) →
  longitudinalCoefficient kernel ≡ 0ℚ - 1ℚ
longitudinalIsMinusOne kernel =
  let
    z = waveCoefficient kernel
    y = longitudinalCoefficient kernel

    differenceEquality :
      (z + y) - z ≡ 0ℚ - 1ℚ
    differenceEquality =
      cong₂ _-_ (wardSlopeZero kernel) (waveNormalized kernel)

    leftNormalForm : (z + y) - z ≡ y
    leftNormalForm = ℚRing.solve-∀ z y
  in
  trans (sym leftNormalForm) differenceEquality

------------------------------------------------------------------------
-- Coefficient-level Maxwell identification.
------------------------------------------------------------------------

deltaCoefficient : LocalTwoDerivativeWardKernel → ℚ → ℚ
deltaCoefficient kernel momentumSquared =
  massSquared kernel + waveCoefficient kernel * momentumSquared

maxwellDeltaCoefficient : ℚ → ℚ
maxwellDeltaCoefficient momentumSquared = momentumSquared

maxwellLongitudinalCoefficient : ℚ
maxwellLongitudinalCoefficient = 0ℚ - 1ℚ

deltaCoefficientIsMaxwell :
  (kernel : LocalTwoDerivativeWardKernel) →
  ∀ momentumSquared →
  deltaCoefficient kernel momentumSquared
  ≡ maxwellDeltaCoefficient momentumSquared
deltaCoefficientIsMaxwell kernel momentumSquared
  rewrite wardMassTermZero kernel
        | waveNormalized kernel =
  ℚRing.solve-∀ momentumSquared

longitudinalCoefficientIsMaxwell :
  (kernel : LocalTwoDerivativeWardKernel) →
  longitudinalCoefficient kernel ≡ maxwellLongitudinalCoefficient
longitudinalCoefficientIsMaxwell = longitudinalIsMinusOne

record MaxwellQuadraticKernelClassification
    (kernel : LocalTwoDerivativeWardKernel) : Set where
  field
    massTermZero : massSquared kernel ≡ 0ℚ
    waveIsOne : waveCoefficient kernel ≡ 1ℚ
    longitudinalIsMinusOne :
      longitudinalCoefficient kernel ≡ maxwellLongitudinalCoefficient
    deltaIsMomentumSquared : ∀ q →
      deltaCoefficient kernel q ≡ maxwellDeltaCoefficient q

open MaxwellQuadraticKernelClassification public

classifyLocalWardKernelAsMaxwell :
  (kernel : LocalTwoDerivativeWardKernel) →
  MaxwellQuadraticKernelClassification kernel
classifyLocalWardKernelAsMaxwell kernel = record
  { massTermZero = wardMassTermZero kernel
  ; waveIsOne = waveNormalized kernel
  ; longitudinalIsMinusOne = longitudinalIsMinusOne kernel
  ; deltaIsMomentumSquared = deltaCoefficientIsMaxwell kernel
  }

------------------------------------------------------------------------
-- Proof-level classification.
------------------------------------------------------------------------

localWardKernelClassificationLevel : ProofLevel
localWardKernelClassificationLevel = machineChecked

-- The physical producer is now much narrower: show that the SAME Gaussian
-- continuum Yang--Mills Schwinger family has the local two-derivative O(4)
-- tensor form above and that its exact gauge Ward identity specializes to the
-- two displayed nonzero momenta.  The coefficient classification itself is no
-- longer a physical assumption.
physicalGaussianYMProvidesLocalWardKernelLevel : ProofLevel
physicalGaussianYMProvidesLocalWardKernelLevel = conditional
