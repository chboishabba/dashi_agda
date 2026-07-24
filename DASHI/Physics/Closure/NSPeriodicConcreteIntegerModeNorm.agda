module DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (ℤ; +_; -[1+_])

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using
  (Vec3; vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicModeInverseNormScaling as Scaling
import DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws as Ordered
open Ordered using (realVecNormSquared)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal natural squared norm of an integer Fourier mode.
------------------------------------------------------------------------

data PositiveNat : Nat → Set where
  positive-suc : ∀ n → PositiveNat (suc n)

natSquare : Nat → Nat
natSquare n = n * n

modeNatNormSquared : Z3.FourierMode → Nat
modeNatNormSquared (Z3.mode x y z) =
  natSquare (Cube.integerMagnitude x) +
    (natSquare (Cube.integerMagnitude y) +
      natSquare (Cube.integerMagnitude z))

positiveSquare : ∀ {n} → PositiveNat n → PositiveNat (natSquare n)
positiveSquare (positive-suc n) = positive-suc _

positivePlusLeft :
  ∀ {a b} → PositiveNat a → PositiveNat (a + b)
positivePlusLeft (positive-suc n) = positive-suc _

positivePlusRight :
  ∀ {a b} → PositiveNat b → PositiveNat (a + b)
positivePlusRight {a = zero} proof = proof
positivePlusRight {a = suc a} proof = positive-suc _

nonzeroModeNatNormPositive :
  ∀ k → Z3.NonZeroMode k → PositiveNat (modeNatNormSquared k)
nonzeroModeNatNormPositive
  (Z3.mode (+ zero) (+ zero) (+ zero)) nonzero =
  ⊥-elim (Z3.notZero nonzero refl)
nonzeroModeNatNormPositive
  (Z3.mode (+ zero) (+ zero) (+ (suc z))) nonzero =
  positivePlusRight (positivePlusRight (positiveSquare (positive-suc z)))
nonzeroModeNatNormPositive
  (Z3.mode (+ zero) (+ zero) (-[1+ z ])) nonzero =
  positivePlusRight (positivePlusRight (positiveSquare (positive-suc z)))
nonzeroModeNatNormPositive
  (Z3.mode (+ zero) (+ (suc y)) z) nonzero =
  positivePlusRight
    (positivePlusLeft (positiveSquare (positive-suc y)))
nonzeroModeNatNormPositive
  (Z3.mode (+ zero) (-[1+ y ]) z) nonzero =
  positivePlusRight
    (positivePlusLeft (positiveSquare (positive-suc y)))
nonzeroModeNatNormPositive
  (Z3.mode (+ (suc x)) y z) nonzero =
  positivePlusLeft (positiveSquare (positive-suc x))
nonzeroModeNatNormPositive
  (Z3.mode (-[1+ x ]) y z) nonzero =
  positivePlusLeft (positiveSquare (positive-suc x))

------------------------------------------------------------------------
-- Coherent integer-to-real embedding.
--
-- The combinatorial theorem above is fully concrete.  The remaining bridge is
-- the ordinary ordered-ring embedding of Z into the repository's real-analysis
-- authority.  It is kept in one record so coordinate embedding, norm meaning and
-- strict positivity cannot be mixed from unrelated carriers.
------------------------------------------------------------------------

record ConcreteIntegerRealNormEmbedding : Set₁ where
  field
    embedInteger : ℤ → ℝ
    embedNat : Nat → ℝ

    embeddedModeNormMeaning : ∀ x y z →
      embedNat
        (natSquare (Cube.integerMagnitude x) +
          (natSquare (Cube.integerMagnitude y) +
            natSquare (Cube.integerMagnitude z)))
      ≡
      realVecNormSquared
        (vec3 (embedInteger x) (embedInteger y) (embedInteger z))

    positiveNatEmbedsPositive : ∀ {n} →
      PositiveNat n → 0ℝ <ℝ embedNat n

open ConcreteIntegerRealNormEmbedding public

integerModeWaveVector :
  ConcreteIntegerRealNormEmbedding → Z3.FourierMode → Vec3 ℝ
integerModeWaveVector E (Z3.mode x y z) =
  vec3 (embedInteger E x) (embedInteger E y) (embedInteger E z)

embeddedModeNormSquared :
  ConcreteIntegerRealNormEmbedding → Z3.FourierMode → ℝ
embeddedModeNormSquared E k = embedNat E (modeNatNormSquared k)

embeddedNonzeroModeNormPositive :
  (E : ConcreteIntegerRealNormEmbedding) →
  ∀ k → Z3.NonZeroMode k →
  0ℝ <ℝ embeddedModeNormSquared E k
embeddedNonzeroModeNormPositive E k nonzero =
  positiveNatEmbedsPositive E
    (nonzeroModeNatNormPositive k nonzero)

concreteIntegerModeNormIdentification :
  ConcreteIntegerRealNormEmbedding →
  Scaling.IntegerModeNormIdentification
concreteIntegerModeNormIdentification E = record
  { modeWaveVector = integerModeWaveVector E
  ; modeNormSquared = embeddedModeNormSquared E
  ; modeNormSquaredMeaning =
      λ where
        (Z3.mode x y z) → embeddedModeNormMeaning E x y z
  ; nonzeroModeNormPositive = embeddedNonzeroModeNormPositive E
  }

record ConcretePeriodicModeNormAuthority : Set₁ where
  field
    realEmbedding : ConcreteIntegerRealNormEmbedding
    squareAuthority : Ordered.OrderedRealSquareAuthority
    inverseAuthority : Scaling.OrderedRealInverseAuthority

open ConcretePeriodicModeNormAuthority public

concreteModeInverseScaling :
  (A : ConcretePeriodicModeNormAuthority) →
  ∀ k → (nonzero : Z3.NonZeroMode k) →
  Scaling.ExactModeInverseNormScaling
    (inverseAuthority A)
    (concreteIntegerModeNormIdentification (realEmbedding A))
    k nonzero
concreteModeInverseScaling A =
  Scaling.exactModeInverseNormScaling
    (inverseAuthority A)
    (concreteIntegerModeNormIdentification (realEmbedding A))

------------------------------------------------------------------------
-- Status: k /= 0 implies a strictly positive literal Nat squared norm without
-- any analytic assumption.  The only remaining authority is the standard
-- positivity-preserving integer-to-real embedding and reciprocal field law.
------------------------------------------------------------------------

concreteIntegerModeNormLevel : ProofLevel
concreteIntegerModeNormLevel = machineChecked
