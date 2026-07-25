module DASHI.Physics.Closure.NSPeriodicConcreteModeOperatorPythagorean where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; _≤ℝ_
  ; ≤ℝ-refl
  ; ≤ℝ-trans
  ; +-mono-≤
  ; +-identityˡ
  ; +-identityʳ
  ; +-assoc
  ; +-comm
  )
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier using
  (Vec3; vec3)
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSPeriodicModeInverseNormScaling as Scaling
import DASHI.Physics.Closure.NSPeriodicRealOrderedNormLaws as Ordered
import DASHI.Physics.Closure.NSPeriodicRealBiotSavartModeNorm as RealMode
import DASHI.Physics.Closure.NSPeriodicFinitePythagoreanSum as Finite
import DASHI.Physics.Closure.NSPeriodicLerayBiotSavartNormReduction as Operator
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The standard ordered-real cancellation law needed to use the generic
-- absorption arithmetic as a norm arithmetic.  All other fields are already
-- supplied by the repository's real-analysis authority.
------------------------------------------------------------------------

record RealOrderCancellationAuthority : Set₁ where
  field
    addOrderCancelRight : ∀ {a b c : ℝ} →
      (a +ℝ c) ≤ℝ (b +ℝ c) → a ≤ℝ b

open RealOrderCancellationAuthority public

realNormArithmetic :
  RealOrderCancellationAuthority → AbsorptionArithmetic
realNormArithmetic O = record
  { Scalar = ℝ
  ; zero = 0ℝ
  ; _+_ = _+ℝ_
  ; _≤_ = _≤ℝ_
  ; ≤-trans = ≤ℝ-trans
  ; addZeroLeft = +-identityˡ
  ; addAssociative = +-assoc
  ; addCommutative = +-comm
  ; additionMonotoneLeft =
      λ a≤b → +-mono-≤ ≤ℝ-refl a≤b
  ; additionMonotoneRight =
      λ a≤b → +-mono-≤ a≤b ≤ℝ-refl
  ; additionCancelRight = addOrderCancelRight O
  }

------------------------------------------------------------------------
-- Exact zero/nonzero classification for Z^3.
------------------------------------------------------------------------

data ModeZeroDecision (k : Z3.FourierMode) : Set where
  is-zero : k ≡ Z3.zeroMode → ModeZeroDecision k
  is-nonzero : Z3.NonZeroMode k → ModeZeroDecision k

decideModeZero : ∀ k → ModeZeroDecision k
decideModeZero (Z3.mode (+ zero) (+ zero) (+ zero)) = is-zero refl
decideModeZero (Z3.mode (+ zero) (+ zero) (+ (suc z))) =
  is-nonzero (record { notZero = λ () })
decideModeZero (Z3.mode (+ zero) (+ zero) (-[1+ z ])) =
  is-nonzero (record { notZero = λ () })
decideModeZero (Z3.mode (+ zero) (+ (suc y)) z) =
  is-nonzero (record { notZero = λ () })
decideModeZero (Z3.mode (+ zero) (-[1+ y ]) z) =
  is-nonzero (record { notZero = λ () })
decideModeZero (Z3.mode (+ (suc x)) y z) =
  is-nonzero (record { notZero = λ () })
decideModeZero (Z3.mode (-[1+ x ]) y z) =
  is-nonzero (record { notZero = λ () })

------------------------------------------------------------------------
-- Coherent modewise inverse and Euclidean split.
------------------------------------------------------------------------

modeNormIdentification :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  Scaling.IntegerModeNormIdentification
modeNormIdentification A =
  ModeNorm.concreteIntegerModeNormIdentification
    (ModeNorm.realEmbedding A)

modeInverseNormSquared :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  Z3.FourierMode → ℝ
modeInverseNormSquared A k =
  Scaling.inverseNormSquared
    (ModeNorm.inverseAuthority A)
    (modeNormIdentification A)
    k

modeInverseNormLaw :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  ∀ k → Z3.NonZeroMode k →
  modeInverseNormSquared A k
    *ℝ Scaling.modeNormSquared (modeNormIdentification A) k
  ≡ 1ℝ
modeInverseNormLaw A k nonzero =
  Scaling.inverseNormSquaredTimesNormSquared
    (ModeNorm.inverseAuthority A)
    (modeNormIdentification A)
    k
    nonzero

modeInverseNormNonnegative :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  ∀ k → Z3.NonZeroMode k →
  0ℝ ≤ℝ modeInverseNormSquared A k
modeInverseNormNonnegative A k nonzero =
  Scaling.inverseNormSquaredNonnegative
    (ModeNorm.inverseAuthority A)
    (modeNormIdentification A)
    k
    nonzero

realModeInverseInputs :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  ∀ k → Z3.NonZeroMode k → Vec3 ℝ →
  RealMode.RealModeInverseNormInputs
realModeInverseInputs A k nonzero omega
  with ModeNorm.integerModeWaveVector (ModeNorm.realEmbedding A) k | omega
... | vec3 k₁ k₂ k₃ | vec3 w₁ w₂ w₃ = record
  { k₁ = k₁
  ; k₂ = k₂
  ; k₃ = k₃
  ; w₁ = w₁
  ; w₂ = w₂
  ; w₃ = w₃
  ; inverseNormSquared = modeInverseNormSquared A k
  ; inverseNormLaw =
      subst
        (λ normSquared →
          modeInverseNormSquared A k *ℝ normSquared ≡ 1ℝ)
        (Scaling.modeNormSquaredMeaning (modeNormIdentification A) k)
        (modeInverseNormLaw A k nonzero)
  }

nonzeroLongitudinalComplementNonnegative :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  ∀ k → (nonzero : Z3.NonZeroMode k) → (coefficient : Vec3 ℝ) →
  0ℝ ≤ℝ
    RealMode.modeVorticityLongitudinalSquared
      (realModeInverseInputs A k nonzero coefficient)
nonzeroLongitudinalComplementNonnegative A k nonzero coefficient =
  Ordered.realLongitudinalComplementNonnegative
    (ModeNorm.squareAuthority A)
    (ModeNorm.integerModeWaveVector (ModeNorm.realEmbedding A) k)
    coefficient
    (modeInverseNormSquared A k)
    (modeInverseNormNonnegative A k nonzero)

------------------------------------------------------------------------
-- Zero-safe Leray mode family.
--
-- At k = 0 the Leray projector is the identity.  At nonzero k its squared
-- norm is represented by |k|^{-2}|k x v|^2 and the complementary longitudinal
-- square is |k|^{-2}(k . v)^2.
------------------------------------------------------------------------

lerayModeInput :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
lerayModeInput A coefficient k =
  Ordered.realVecNormSquared (coefficient k)

lerayModeOutput :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
lerayModeOutput A coefficient k with decideModeZero k
... | is-zero equality = Ordered.realVecNormSquared (coefficient k)
... | is-nonzero nonzero =
  RealMode.modeBiotSavartH1Squared
    (realModeInverseInputs A k nonzero (coefficient k))

lerayModeComplement :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
lerayModeComplement A coefficient k with decideModeZero k
... | is-zero equality = 0ℝ
... | is-nonzero nonzero =
  RealMode.modeVorticityLongitudinalSquared
    (realModeInverseInputs A k nonzero (coefficient k))

lerayModeComplementNonnegative :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  ∀ k → 0ℝ ≤ℝ lerayModeComplement A coefficient k
lerayModeComplementNonnegative A coefficient k with decideModeZero k
... | is-zero equality = ≤ℝ-refl
... | is-nonzero nonzero =
  nonzeroLongitudinalComplementNonnegative A k nonzero (coefficient k)

lerayModeSplit :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  ∀ k →
  lerayModeInput A coefficient k
  ≡ lerayModeOutput A coefficient k +ℝ lerayModeComplement A coefficient k
lerayModeSplit A coefficient k with decideModeZero k
... | is-zero equality =
  sym (+-identityʳ (Ordered.realVecNormSquared (coefficient k)))
... | is-nonzero nonzero =
  RealMode.modeBiotSavartPythagoreanIdentity
    (realModeInverseInputs A k nonzero (coefficient k))

lerayModeFamily :
  (O : RealOrderCancellationAuthority) →
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Finite.ModewisePythagoreanFamily
    (realNormArithmetic O)
    Z3.FourierMode
lerayModeFamily O A coefficient = record
  { input = lerayModeInput A coefficient
  ; output = lerayModeOutput A coefficient
  ; complement = lerayModeComplement A coefficient
  ; complementNonnegative = lerayModeComplementNonnegative A coefficient
  ; modewiseSplit = lerayModeSplit A coefficient
  }

------------------------------------------------------------------------
-- Zero-safe Biot-Savart mode family.
--
-- Vorticity has no zero Fourier mode.  The literal homogeneous sum therefore
-- assigns zero input, output, and complement at k = 0.  Every nonzero mode uses
-- the exact inverse-norm/Lagrange identity above.
------------------------------------------------------------------------

biotSavartModeInput :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
biotSavartModeInput A coefficient k with decideModeZero k
... | is-zero equality = 0ℝ
... | is-nonzero nonzero =
  RealMode.modeVorticityNormSquared
    (realModeInverseInputs A k nonzero (coefficient k))

biotSavartModeOutput :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
biotSavartModeOutput A coefficient k with decideModeZero k
... | is-zero equality = 0ℝ
... | is-nonzero nonzero =
  RealMode.modeBiotSavartH1Squared
    (realModeInverseInputs A k nonzero (coefficient k))

biotSavartModeComplement :
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Z3.FourierMode → ℝ
biotSavartModeComplement A coefficient k with decideModeZero k
... | is-zero equality = 0ℝ
... | is-nonzero nonzero =
  RealMode.modeVorticityLongitudinalSquared
    (realModeInverseInputs A k nonzero (coefficient k))

biotSavartModeComplementNonnegative :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  ∀ k → 0ℝ ≤ℝ biotSavartModeComplement A coefficient k
biotSavartModeComplementNonnegative A coefficient k with decideModeZero k
... | is-zero equality = ≤ℝ-refl
... | is-nonzero nonzero =
  nonzeroLongitudinalComplementNonnegative A k nonzero (coefficient k)

biotSavartModeSplit :
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (coefficient : Z3.FourierMode → Vec3 ℝ) →
  ∀ k →
  biotSavartModeInput A coefficient k
  ≡ biotSavartModeOutput A coefficient k
      +ℝ biotSavartModeComplement A coefficient k
biotSavartModeSplit A coefficient k with decideModeZero k
... | is-zero equality = sym (+-identityˡ 0ℝ)
... | is-nonzero nonzero =
  RealMode.modeBiotSavartPythagoreanIdentity
    (realModeInverseInputs A k nonzero (coefficient k))

biotSavartModeFamily :
  (O : RealOrderCancellationAuthority) →
  ModeNorm.ConcretePeriodicModeNormAuthority →
  (Z3.FourierMode → Vec3 ℝ) →
  Finite.ModewisePythagoreanFamily
    (realNormArithmetic O)
    Z3.FourierMode
biotSavartModeFamily O A coefficient = record
  { input = biotSavartModeInput A coefficient
  ; output = biotSavartModeOutput A coefficient
  ; complement = biotSavartModeComplement A coefficient
  ; complementNonnegative = biotSavartModeComplementNonnegative A coefficient
  ; modewiseSplit = biotSavartModeSplit A coefficient
  }

------------------------------------------------------------------------
-- Literal cutoff sums and the combined official operator decomposition.
------------------------------------------------------------------------

lerayInputCutoffSum lerayOutputCutoffSum lerayComplementCutoffSum :
  (O : RealOrderCancellationAuthority) →
  ModeNorm.ConcretePeriodicModeNormAuthority →
  Nat →
  (Z3.FourierMode → Vec3 ℝ) →
  ℝ
lerayInputCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.input (lerayModeFamily O A coefficient))
    (Cube.cutoffModes N)
lerayOutputCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.output (lerayModeFamily O A coefficient))
    (Cube.cutoffModes N)
lerayComplementCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.complement (lerayModeFamily O A coefficient))
    (Cube.cutoffModes N)

biotSavartInputCutoffSum biotSavartOutputCutoffSum
  biotSavartComplementCutoffSum :
  (O : RealOrderCancellationAuthority) →
  ModeNorm.ConcretePeriodicModeNormAuthority →
  Nat →
  (Z3.FourierMode → Vec3 ℝ) →
  ℝ
biotSavartInputCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.input (biotSavartModeFamily O A coefficient))
    (Cube.cutoffModes N)
biotSavartOutputCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.output (biotSavartModeFamily O A coefficient))
    (Cube.cutoffModes N)
biotSavartComplementCutoffSum O A N coefficient =
  Finite.sumBy
    (Finite.complement (biotSavartModeFamily O A coefficient))
    (Cube.cutoffModes N)

concreteCutoffOperatorNormInputs :
  (O : RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (velocityCoefficient vorticityCoefficient :
    Z3.FourierMode → Vec3 ℝ) →
  Operator.PeriodicLerayBiotSavartNormInputs (realNormArithmetic O)
concreteCutoffOperatorNormInputs O A N velocityCoefficient vorticityCoefficient =
  record
    { lerayInputNormSquared =
        lerayInputCutoffSum O A N velocityCoefficient
    ; lerayOutputNormSquared =
        lerayOutputCutoffSum O A N velocityCoefficient
    ; lerayLongitudinalNormSquared =
        lerayComplementCutoffSum O A N velocityCoefficient
    ; vorticityNormSquared =
        biotSavartInputCutoffSum O A N vorticityCoefficient
    ; biotSavartHomogeneousH1Squared =
        biotSavartOutputCutoffSum O A N vorticityCoefficient
    ; vorticityLongitudinalNormSquared =
        biotSavartComplementCutoffSum O A N vorticityCoefficient
    ; lerayLongitudinalNonnegative =
        Finite.sumByNonnegative
          (Finite.complement (lerayModeFamily O A velocityCoefficient))
          (Finite.complementNonnegative
            (lerayModeFamily O A velocityCoefficient))
          (Cube.cutoffModes N)
    ; vorticityLongitudinalNonnegative =
        Finite.sumByNonnegative
          (Finite.complement (biotSavartModeFamily O A vorticityCoefficient))
          (Finite.complementNonnegative
            (biotSavartModeFamily O A vorticityCoefficient))
          (Cube.cutoffModes N)
    ; lerayPythagoreanIdentity =
        Finite.sumByPythagoreanSplit
          (lerayModeFamily O A velocityCoefficient)
          (Cube.cutoffModes N)
    ; biotSavartCrossProductIdentity =
        Finite.sumByPythagoreanSplit
          (biotSavartModeFamily O A vorticityCoefficient)
          (Cube.cutoffModes N)
    }

concreteCutoffLerayContractive :
  (O : RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (velocityCoefficient : Z3.FourierMode → Vec3 ℝ) →
  lerayOutputCutoffSum O A N velocityCoefficient
  ≤ℝ lerayInputCutoffSum O A N velocityCoefficient
concreteCutoffLerayContractive O A N velocityCoefficient =
  Operator.periodicLerayProjectionContractive
    (concreteCutoffOperatorNormInputs
      O A N velocityCoefficient velocityCoefficient)

concreteCutoffBiotSavartBounded :
  (O : RealOrderCancellationAuthority) →
  (A : ModeNorm.ConcretePeriodicModeNormAuthority) →
  (N : Nat) →
  (vorticityCoefficient : Z3.FourierMode → Vec3 ℝ) →
  biotSavartOutputCutoffSum O A N vorticityCoefficient
  ≤ℝ biotSavartInputCutoffSum O A N vorticityCoefficient
concreteCutoffBiotSavartBounded O A N vorticityCoefficient =
  Operator.periodicBiotSavartHomogeneousH1Bounded
    (concreteCutoffOperatorNormInputs
      O A N vorticityCoefficient vorticityCoefficient)

------------------------------------------------------------------------
-- Status: the literal duplicate-free cutoff cube now carries exact finite-sum
-- Leray contractivity and Biot-Savart H1 boundedness with constant one.  The
-- only remaining carrier inputs are foundational ordered-real embedding,
-- reciprocal, square, and order-cancellation laws; no cutoff-dependent or PDE
-- operator estimate remains in this lane.
------------------------------------------------------------------------

concreteModeOperatorPythagoreanLevel : ProofLevel
concreteModeOperatorPythagoreanLevel = machineChecked
