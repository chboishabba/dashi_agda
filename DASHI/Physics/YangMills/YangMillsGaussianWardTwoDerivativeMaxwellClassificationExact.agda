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
-- Gaussianity alone does NOT imply Maxwell. The physical local-field theorem
-- must first identify the hypothetical Gaussian continuum kernel as the local
-- O(4)-covariant two-derivative form
--
--   K_{mu nu}(p)
--     = (m^2 + Z p^2) delta_{mu nu} + Y p_mu p_nu
--
-- and specialize the SAME exact Ward identity at two distinct nonzero p^2.
--
-- The generic theorem below deliberately does not assume rational continuum
-- coefficients. It uses only the cancellative additive-group laws shared by
-- the real/Bishop-real coefficient carrier. Writing s=Z+Y, Ward at p^2=1 and
-- p^2=2 has the additive shape
--
--   m+s=0,        (m+s)+s=0.
--
-- Hence s=0 and then m=0. Standard kinetic normalization Z=1 and cancellation
-- against 1+(-1)=0 force Y=-1. This is the algebraic heart of the
-- Gaussian/Ward -> Maxwell reductio, independent of a rational approximation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Generic continuum coefficient algebra.
------------------------------------------------------------------------

record WardCoefficientAdditiveGroup : Set₁ where
  field
    Scalar : Set
    zero one negOne : Scalar
    add : Scalar → Scalar → Scalar

    zeroLeft : ∀ x → add zero x ≡ x
    zeroRight : ∀ x → add x zero ≡ x
    cancelLeft : ∀ a b c → add a b ≡ add a c → b ≡ c
    onePlusNegOneZero : add one negOne ≡ zero

open WardCoefficientAdditiveGroup public

record GenericLocalTwoDerivativeWardKernel
    (A : WardCoefficientAdditiveGroup) : Set where
  field
    massSquared waveCoefficient longitudinalCoefficient : Scalar A

    -- These are Ward evaluations at two distinct nonzero momentum squares.
    -- At p^2=1: m+s=0. At p^2=2: m+2s=0, written as (m+s)+s=0
    -- to require only additive-group structure in the compiler.
    wardAtOne :
      add A massSquared (add A waveCoefficient longitudinalCoefficient)
      ≡ zero A

    wardAtTwo :
      add A
        (add A massSquared (add A waveCoefficient longitudinalCoefficient))
        (add A waveCoefficient longitudinalCoefficient)
      ≡ zero A

    waveNormalized : waveCoefficient ≡ one A

open GenericLocalTwoDerivativeWardKernel public

genericWardSlopeZero :
  (A : WardCoefficientAdditiveGroup) →
  (kernel : GenericLocalTwoDerivativeWardKernel A) →
  add A (waveCoefficient kernel) (longitudinalCoefficient kernel) ≡ zero A
genericWardSlopeZero A kernel =
  let
    m = massSquared kernel
    s = add A (waveCoefficient kernel) (longitudinalCoefficient kernel)

    shiftedWardOne :
      add A (add A m s) s ≡ add A (zero A) s
    shiftedWardOne = cong (λ x → add A x s) (wardAtOne kernel)

    zeroPlusSlopeIsZero : add A (zero A) s ≡ zero A
    zeroPlusSlopeIsZero =
      trans (sym shiftedWardOne) (wardAtTwo kernel)
  in
  trans (sym (zeroLeft A s)) zeroPlusSlopeIsZero

genericWardMassTermZero :
  (A : WardCoefficientAdditiveGroup) →
  (kernel : GenericLocalTwoDerivativeWardKernel A) →
  massSquared kernel ≡ zero A
genericWardMassTermZero A kernel =
  let
    m = massSquared kernel
    s = add A (waveCoefficient kernel) (longitudinalCoefficient kernel)

    shiftedSlopeZero : add A m s ≡ add A m (zero A)
    shiftedSlopeZero =
      cong (λ x → add A m x) (genericWardSlopeZero A kernel)

    massPlusZeroIsZero : add A m (zero A) ≡ zero A
    massPlusZeroIsZero =
      trans (sym shiftedSlopeZero) (wardAtOne kernel)
  in
  trans (sym (zeroRight A m)) massPlusZeroIsZero

genericWardLongitudinalIsMinusOne :
  (A : WardCoefficientAdditiveGroup) →
  (kernel : GenericLocalTwoDerivativeWardKernel A) →
  longitudinalCoefficient kernel ≡ negOne A
genericWardLongitudinalIsMinusOne A kernel =
  let
    z = waveCoefficient kernel
    y = longitudinalCoefficient kernel

    normalizedSum :
      add A z y ≡ add A (one A) y
    normalizedSum = cong (λ x → add A x y) (waveNormalized kernel)

    onePlusYIsZero : add A (one A) y ≡ zero A
    onePlusYIsZero =
      trans (sym normalizedSum) (genericWardSlopeZero A kernel)

    sameLeftHandSide :
      add A (one A) y ≡ add A (one A) (negOne A)
    sameLeftHandSide =
      trans onePlusYIsZero (sym (onePlusNegOneZero A))
  in
  cancelLeft A (one A) y (negOne A) sameLeftHandSide

record GenericMaxwellQuadraticKernelClassification
    (A : WardCoefficientAdditiveGroup)
    (kernel : GenericLocalTwoDerivativeWardKernel A) : Set where
  field
    massTermZero : massSquared kernel ≡ zero A
    waveIsOne : waveCoefficient kernel ≡ one A
    longitudinalIsMinusOne : longitudinalCoefficient kernel ≡ negOne A
    wardSlopeIsZero :
      add A (waveCoefficient kernel) (longitudinalCoefficient kernel) ≡ zero A

open GenericMaxwellQuadraticKernelClassification public

classifyGenericLocalWardKernelAsMaxwell :
  (A : WardCoefficientAdditiveGroup) →
  (kernel : GenericLocalTwoDerivativeWardKernel A) →
  GenericMaxwellQuadraticKernelClassification A kernel
classifyGenericLocalWardKernelAsMaxwell A kernel = record
  { massTermZero = genericWardMassTermZero A kernel
  ; waveIsOne = waveNormalized kernel
  ; longitudinalIsMinusOne = genericWardLongitudinalIsMinusOne A kernel
  ; wardSlopeIsZero = genericWardSlopeZero A kernel
  }

------------------------------------------------------------------------
-- Executable rational specialization retained as a finite regression/calibration
-- surface. The Clay dependency uses the generic theorem above, not a premise
-- that continuum coefficients happen to be rational.
------------------------------------------------------------------------

record LocalTwoDerivativeWardKernel : Set where
  field
    massSquared waveCoefficient longitudinalCoefficient : ℚ
    wardAtOne :
      massSquared + (waveCoefficient + longitudinalCoefficient) * 1ℚ ≡ 0ℚ
    wardAtTwo :
      massSquared + (waveCoefficient + longitudinalCoefficient) * (+ 2 / 1)
      ≡ 0ℚ
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
      (m + s * (+ 2 / 1)) - (m + s * 1ℚ) ≡ 0ℚ - 0ℚ
    differenceEquality = cong₂ _-_ (wardAtTwo kernel) (wardAtOne kernel)
    leftNormalForm :
      (m + s * (+ 2 / 1)) - (m + s * 1ℚ) ≡ s
    leftNormalForm = ℚRing.solve-∀ m s
    rightNormalForm : 0ℚ - 0ℚ ≡ 0ℚ
    rightNormalForm = ℚRing.solve []
  in
  trans (sym leftNormalForm) (trans differenceEquality rightNormalForm)

wardMassTermZero :
  (kernel : LocalTwoDerivativeWardKernel) → massSquared kernel ≡ 0ℚ
wardMassTermZero kernel =
  let
    m = massSquared kernel
    s = waveCoefficient kernel + longitudinalCoefficient kernel
    differenceEquality : (m + s * 1ℚ) - s ≡ 0ℚ - 0ℚ
    differenceEquality = cong₂ _-_ (wardAtOne kernel) (wardSlopeZero kernel)
    leftNormalForm : (m + s * 1ℚ) - s ≡ m
    leftNormalForm = ℚRing.solve-∀ m s
    rightNormalForm : 0ℚ - 0ℚ ≡ 0ℚ
    rightNormalForm = ℚRing.solve []
  in
  trans (sym leftNormalForm) (trans differenceEquality rightNormalForm)

wardLongitudinalIsMinusOne :
  (kernel : LocalTwoDerivativeWardKernel) →
  longitudinalCoefficient kernel ≡ 0ℚ - 1ℚ
wardLongitudinalIsMinusOne kernel =
  let
    z = waveCoefficient kernel
    y = longitudinalCoefficient kernel
    differenceEquality : (z + y) - z ≡ 0ℚ - 1ℚ
    differenceEquality = cong₂ _-_ (wardSlopeZero kernel) (waveNormalized kernel)
    leftNormalForm : (z + y) - z ≡ y
    leftNormalForm = ℚRing.solve-∀ z y
  in
  trans (sym leftNormalForm) differenceEquality

deltaCoefficient : LocalTwoDerivativeWardKernel → ℚ → ℚ
deltaCoefficient kernel momentumSquared =
  massSquared kernel + waveCoefficient kernel * momentumSquared

maxwellDeltaCoefficient : ℚ → ℚ
maxwellDeltaCoefficient momentumSquared = momentumSquared

maxwellLongitudinalCoefficient : ℚ
maxwellLongitudinalCoefficient = 0ℚ - 1ℚ

deltaCoefficientIsMaxwell :
  (kernel : LocalTwoDerivativeWardKernel) → ∀ momentumSquared →
  deltaCoefficient kernel momentumSquared ≡ maxwellDeltaCoefficient momentumSquared
deltaCoefficientIsMaxwell kernel momentumSquared
  rewrite wardMassTermZero kernel | waveNormalized kernel =
  ℚRing.solve-∀ momentumSquared

record MaxwellQuadraticKernelClassification
    (kernel : LocalTwoDerivativeWardKernel) : Set where
  field
    massTermZero : massSquared kernel ≡ 0ℚ
    waveIsOne : waveCoefficient kernel ≡ 1ℚ
    longitudinalIsMinusOneExact :
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
  ; longitudinalIsMinusOneExact = wardLongitudinalIsMinusOne kernel
  ; deltaIsMomentumSquared = deltaCoefficientIsMaxwell kernel
  }

genericWardKernelClassificationLevel : ProofLevel
genericWardKernelClassificationLevel = machineChecked

rationalWardKernelRegressionLevel : ProofLevel
rationalWardKernelRegressionLevel = machineChecked

-- The physical producer is now exactly: on the SAME Gaussian continuum
-- Yang--Mills family, construct the local two-derivative O(4) tensor form and
-- specialize the exact Ward identity at the two nonzero momenta. Instantiating
-- the coefficient algebra by the continuum real carrier is not a new estimate.
physicalGaussianYMProvidesLocalWardKernelLevel : ProofLevel
physicalGaussianYMProvidesLocalWardKernelLevel = conditional
