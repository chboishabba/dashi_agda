module DASHI.Physics.Closure.NSDifferentiatedTriadAnalyticLeaf where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel

------------------------------------------------------------------------
-- Concrete differentiated Fourier-triad analytic leaf.
--
-- Pointwise in one resonant triad; consequently no Galerkin-cutoff parameter
-- occurs in the theorem or its constant.  The existing finite incidence and
-- Schur modules own the later summation/transport step.
------------------------------------------------------------------------

record TriadAnalyticLaws
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    fourier : FourierVectorLaws Mode Vector Scalar

    absolute : Scalar → Scalar
    norm : Vector → Scalar
    modeNorm : Mode → Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    lerayProject : Mode → Vector → Vector

    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    +-mono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)

    norm-vectorAdd :
      ∀ x y → norm (vectorAdd fourier x y) ≤ (norm x + norm y)

    inverse-square-cross-bound :
      ∀ p a →
      norm (biotSavartVelocity fourier p a)
        ≤ (inverseNormSquared fourier p * (modeNorm p * norm a))

open TriadAnalyticLaws public

------------------------------------------------------------------------
-- Biot-Savart and projected interaction.
------------------------------------------------------------------------

biot-savart-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (p : Mode) (a : Vector) →
  _≤_ A
    (norm A (biotSavartVelocity (fourier A) p a))
    (_*_ A
      (inverseNormSquared (fourier A) p)
      (_*_ A (modeNorm A p) (norm A a)))
biot-savart-bound A = inverse-square-cross-bound A

projectedInteraction :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  TriadAnalyticLaws Mode Vector Scalar →
  Mode → Mode → Mode → Vector → Vector → Vector
projectedInteraction A k p q a b =
  lerayProject A k
    (vectorScale (fourier A)
      (vectorDot (fourier A)
        (biotSavartVelocity (fourier A) p a)
        (waveVector (fourier A) q))
      b)

interactionMajorant :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  TriadAnalyticLaws Mode Vector Scalar →
  Mode → Mode → Vector → Vector → Scalar
interactionMajorant A p q a b =
  _*_ A
    (_*_ A
      (inverseNormSquared (fourier A) p)
      (modeNorm A p))
    (_*_ A
      (modeNorm A q)
      (_*_ A (norm A a) (norm A b)))

record ProjectedInteractionBound
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (m ⊔ v ⊔ s) where
  field
    projected-interaction-bound :
      ∀ k p q a b →
      _≤_ A
        (norm A (projectedInteraction A k p q a b))
        (interactionMajorant A p q a b)

open ProjectedInteractionBound public

projected-interaction-bound-theorem :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (k p q : Mode) (a b : Vector) →
  _≤_ A
    (norm A (projectedInteraction A k p q a b))
    (interactionMajorant A p q a b)
projected-interaction-bound-theorem A P = projected-interaction-bound P

------------------------------------------------------------------------
-- Both differentiated placements.
------------------------------------------------------------------------

differentiatedProjectedTriad :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  TriadAnalyticLaws Mode Vector Scalar →
  Mode → Mode → Mode →
  Vector → Vector → Vector → Vector → Vector
differentiatedProjectedTriad A k p q uP uQ hP hQ =
  vectorAdd (fourier A)
    (projectedInteraction A k p q hP uQ)
    (projectedInteraction A k p q uP hQ)

differentiatedTriadMajorant :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  TriadAnalyticLaws Mode Vector Scalar →
  Mode → Mode →
  Vector → Vector → Vector → Vector → Scalar
differentiatedTriadMajorant A p q uP uQ hP hQ =
  _+_ A
    (interactionMajorant A p q hP uQ)
    (interactionMajorant A p q uP hQ)

differentiated-product-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (k p q : Mode)
    (uP uQ hP hQ : Vector) →
  _≤_ A
    (norm A (differentiatedProjectedTriad A k p q uP uQ hP hQ))
    (differentiatedTriadMajorant A p q uP uQ hP hQ)
differentiated-product-bound A P k p q uP uQ hP hQ =
  ≤-trans A
    (norm-vectorAdd A
      (projectedInteraction A k p q hP uQ)
      (projectedInteraction A k p q uP hQ))
    (+-mono A
      (projected-interaction-bound P k p q hP uQ)
      (projected-interaction-bound P k p q uP hQ))

------------------------------------------------------------------------
-- Reality-pair folding: completeness, soundness, and no double counting.
------------------------------------------------------------------------

record RealityPairFolding
    {m : Level}
    (Mode : Set m) : Set (lsuc m) where
  field
    negateMode : Mode → Mode
    incidence : Mode → Mode → Mode → Set m
    foldedIncidence : Mode → Mode → Mode → Set m

    negate-involutive : ∀ k → negateMode (negateMode k) ≡ k

    fold-complete :
      ∀ k p q → incidence k p q → foldedIncidence k p q

    fold-sound :
      ∀ k p q → foldedIncidence k p q → incidence k p q

    conjugate-incidence :
      ∀ k p q →
      incidence k p q →
      incidence (negateMode k) (negateMode p) (negateMode q)

    fold-does-not-double-count :
      ∀ k p q →
      foldedIncidence k p q →
      foldedIncidence (negateMode k) (negateMode p) (negateMode q) →
      incidence k p q

open RealityPairFolding public

reality-pair-folding-complete :
  ∀ {m} {Mode : Set m} (F : RealityPairFolding Mode) →
  ∀ k p q → incidence F k p q → foldedIncidence F k p q
reality-pair-folding-complete F = fold-complete F

reality-pair-folding-sound :
  ∀ {m} {Mode : Set m} (F : RealityPairFolding Mode) →
  ∀ k p q → foldedIncidence F k p q → incidence F k p q
reality-pair-folding-sound F = fold-sound F

------------------------------------------------------------------------
-- Tangent correction preserving divergence-free and target-energy tangent.
------------------------------------------------------------------------

record TargetEnergyTangentProjection
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    projectTangent : Mode → Vector → Vector → Vector
    divergenceFree : Mode → Vector → Set s
    targetEnergyDerivativeZero : Mode → Vector → Vector → Set s
    correctionConstant : Scalar

    tangent-divergence-free :
      ∀ k u h →
      divergenceFree k h →
      divergenceFree k (projectTangent k u h)

    tangent-energy-fixed :
      ∀ k u h →
      targetEnergyDerivativeZero k u (projectTangent k u h)

    tangent-norm-bound :
      ∀ k u h →
      _≤_ A
        (norm A (projectTangent k u h))
        (_*_ A correctionConstant (norm A h))

open TargetEnergyTangentProjection public

tangent-projection-lemma :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {A : TriadAnalyticLaws Mode Vector Scalar}
    (T : TargetEnergyTangentProjection A) →
  ∀ k u h →
  divergenceFree T k h →
  divergenceFree T k (projectTangent T k u h)
tangent-projection-lemma T = tangent-divergence-free T

------------------------------------------------------------------------
-- Actual compact-Gamma numerator reconstruction and sign/absolute treatment.
------------------------------------------------------------------------

record CompactGammaNearResponse
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    numeratorDerivative : Mode → Vector → Scalar
    triadNumerator : Mode → Mode → Mode → Vector → Scalar
    compactGammaCoefficient : Mode → Scalar

    near-response-reconstruction :
      ∀ k p q dTriad →
      numeratorDerivative k dTriad
        ≡ triadNumerator k p q dTriad

    compact-gamma-absolute-bound :
      ∀ k dTriad →
      _≤_ A
        (absolute A (numeratorDerivative k dTriad))
        (_*_ A (absolute A (compactGammaCoefficient k)) (norm A dTriad))

open CompactGammaNearResponse public

record CompactGammaCoefficientMonotonicity
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (m ⊔ v ⊔ s) where
  field
    coefficient-multiplies-bound :
      ∀ c x y →
      _≤_ A x y →
      _≤_ A
        (_*_ A (absolute A c) x)
        (_*_ A (absolute A c) y)

open CompactGammaCoefficientMonotonicity public

compactGammaDifferentiatedTriadMajorant :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (A : TriadAnalyticLaws Mode Vector Scalar) →
  CompactGammaNearResponse A →
  Mode → Mode → Mode →
  Vector → Vector → Vector → Vector → Scalar
compactGammaDifferentiatedTriadMajorant A G k p q uP uQ hP hQ =
  _*_ A
    (absolute A (compactGammaCoefficient G k))
    (differentiatedTriadMajorant A p q uP uQ hP hQ)

concrete-differentiated-triad-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (G : CompactGammaNearResponse A)
    (C : CompactGammaCoefficientMonotonicity A)
    (k p q : Mode)
    (uP uQ hP hQ : Vector) →
  _≤_ A
    (absolute A
      (numeratorDerivative G k
        (differentiatedProjectedTriad A k p q uP uQ hP hQ)))
    (compactGammaDifferentiatedTriadMajorant
      A G k p q uP uQ hP hQ)
concrete-differentiated-triad-bound A P G C k p q uP uQ hP hQ =
  ≤-trans A
    (compact-gamma-absolute-bound G k
      (differentiatedProjectedTriad A k p q uP uQ hP hQ))
    (coefficient-multiplies-bound C
      (compactGammaCoefficient G k)
      (norm A
        (differentiatedProjectedTriad A k p q uP uQ hP hQ))
      (differentiatedTriadMajorant A p q uP uQ hP hQ)
      (differentiated-product-bound A P k p q uP uQ hP hQ))
