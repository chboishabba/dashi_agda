module DASHI.Physics.Closure.NSPeriodicRealFourierVectorLaws where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (ℤ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_; zeroR; oneR; zeroʳ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (Polynomial; _:=_; _:+_; _:*_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel
open import DASHI.Physics.Closure.NSPeriodicBiotSavartTransversality
import DASHI.Physics.Closure.NSPeriodicRealVectorPolynomialIdentities as Polynomial
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact real scalar/vector instance for the frozen Fourier formulas.
--
-- The only carrier-specific data left free are integer embedding, inverse norm
-- squared, mode delta, and the chosen vector majorant.  Dot/scale compatibility,
-- cross-product transversality, and the Lagrange norm identity are proved by
-- computed polynomial normalization over the axiomatic real ring.
------------------------------------------------------------------------

record RealFourierEvaluationInputs : Set₁ where
  field
    integerEmbedR : ℤ → ℝ
    inverseNormSquaredR : FourierMode → ℝ
    modeDeltaR : FourierMode → FourierMode → ℝ
    vectorMajorantR : Vec3 ℝ → ℝ

open RealFourierEvaluationInputs public

realSubtract : ℝ → ℝ → ℝ
realSubtract a b = a +R (-R b)

realExactScalarAlgebra :
  RealFourierEvaluationInputs → ExactScalarAlgebra ℝ
realExactScalarAlgebra I = record
  { zero = zeroR
  ; one = oneR
  ; add = _+R_
  ; subtract = realSubtract
  ; multiply = _*R_
  ; negate = -R_
  ; order = _≤ℝ_
  ; integerEmbed = integerEmbedR I
  }

realExactFourierEvaluation :
  (I : RealFourierEvaluationInputs) →
  ExactFourierEvaluation ℝ (realExactScalarAlgebra I)
realExactFourierEvaluation I = record
  { inverseNormSquared = inverseNormSquaredR I
  ; modeDelta = modeDeltaR I
  ; vectorMajorant = vectorMajorantR I
  }

realFourierVectorLaws :
  (I : RealFourierEvaluationInputs) →
  FourierVectorLaws FourierMode (Vec3 ℝ) ℝ
realFourierVectorLaws I =
  exactFourierVectorLaws
    (realExactScalarAlgebra I)
    (realExactFourierEvaluation I)

scaleDotP :
  ∀ {n} →
  Polynomial n → Polynomial n → Polynomial n →
  Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
scaleDotP x₁ x₂ x₃ c y₁ y₂ y₃ =
  (x₁ :* (c :* y₁))
  :+ ((x₂ :* (c :* y₂)) :+ (x₃ :* (c :* y₃)))

dotScaleRightPolynomial : ∀ x₁ x₂ x₃ c y₁ y₂ y₃ →
  Polynomial.dotR x₁ x₂ x₃ (c *R y₁) (c *R y₂) (c *R y₃)
  ≡
  c *R Polynomial.dotR x₁ x₂ x₃ y₁ y₂ y₃
dotScaleRightPolynomial =
  solveComputed 7
    (λ x₁ x₂ x₃ c y₁ y₂ y₃ →
      scaleDotP x₁ x₂ x₃ c y₁ y₂ y₃
      := (c :* Polynomial.dotP x₁ x₂ x₃ y₁ y₂ y₃))
    computed

realDotScaleRight :
  (I : RealFourierEvaluationInputs) →
  ∀ x coefficient y →
  vectorDot (realFourierVectorLaws I) x
    (vectorScale (realFourierVectorLaws I) coefficient y)
  ≡
  scalarMultiply (realFourierVectorLaws I) coefficient
    (vectorDot (realFourierVectorLaws I) x y)
realDotScaleRight I
  (vec3 x₁ x₂ x₃) coefficient (vec3 y₁ y₂ y₃) =
  dotScaleRightPolynomial x₁ x₂ x₃ coefficient y₁ y₂ y₃

realWaveDotOwnCrossIsZero :
  (I : RealFourierEvaluationInputs) →
  ∀ mode omega →
  vectorDot (realFourierVectorLaws I)
    (waveVector (realFourierVectorLaws I) mode)
    (vectorCross (realFourierVectorLaws I)
      (waveVector (realFourierVectorLaws I) mode) omega)
  ≡ scalarZero (realFourierVectorLaws I)
realWaveDotOwnCrossIsZero I (mode k₁ k₂ k₃) (vec3 w₁ w₂ w₃) =
  Polynomial.waveDotOwnCrossPolynomial
    (integerEmbedR I k₁)
    (integerEmbedR I k₂)
    (integerEmbedR I k₃)
    w₁ w₂ w₃

realMultiplyZeroRight :
  (I : RealFourierEvaluationInputs) →
  ∀ coefficient →
  scalarMultiply (realFourierVectorLaws I) coefficient
    (scalarZero (realFourierVectorLaws I))
  ≡ scalarZero (realFourierVectorLaws I)
realMultiplyZeroRight I coefficient = zeroʳ coefficient

realBiotSavartTransversalityLaws :
  (I : RealFourierEvaluationInputs) →
  FourierBiotSavartTransversalityLaws (realFourierVectorLaws I)
realBiotSavartTransversalityLaws I = record
  { dotScaleRight = realDotScaleRight I
  ; waveDotOwnCrossIsZero = realWaveDotOwnCrossIsZero I
  ; multiplyZeroRight = realMultiplyZeroRight I
  }

realBiotSavartVelocityIsTransverse :
  (I : RealFourierEvaluationInputs) →
  ∀ mode omega →
  vectorDot (realFourierVectorLaws I)
    (waveVector (realFourierVectorLaws I) mode)
    (biotSavartVelocity (realFourierVectorLaws I) mode omega)
  ≡ scalarZero (realFourierVectorLaws I)
realBiotSavartVelocityIsTransverse I =
  biotSavartVelocityIsTransverse
    (realBiotSavartTransversalityLaws I)

realVecNormSquared : Vec3 ℝ → ℝ
realVecNormSquared (vec3 x₁ x₂ x₃) =
  (x₁ *R x₁) +R ((x₂ *R x₂) +R (x₃ *R x₃))

realCrossLagrangeIdentity :
  (I : RealFourierEvaluationInputs) →
  ∀ k w →
  realVecNormSquared
    (vectorCross (realFourierVectorLaws I) k w)
  +R
  (vectorDot (realFourierVectorLaws I) k w
   *R vectorDot (realFourierVectorLaws I) k w)
  ≡
  realVecNormSquared k *R realVecNormSquared w
realCrossLagrangeIdentity I
  (vec3 k₁ k₂ k₃) (vec3 w₁ w₂ w₃) =
  Polynomial.lagrangeCrossProductPolynomial
    k₁ k₂ k₃ w₁ w₂ w₃

------------------------------------------------------------------------
-- Status: cross transversality and the Euclidean Lagrange identity are now
-- concrete theorems in the real Fourier carrier.  Remaining official norm work
-- is order/nonnegativity, inverse-norm scaling, and finite-sum transport.
------------------------------------------------------------------------

realFourierVectorLawLevel : ProofLevel
realFourierVectorLawLevel = machineChecked
