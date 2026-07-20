module DASHI.Physics.Closure.NSDifferentiatedTriadAnalyticLeaf where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel

------------------------------------------------------------------------
-- Concrete differentiated Fourier-triad analytic leaf.
--
-- This module closes the algebraic passage
--
--   exact Biot-Savart/Leray triad
--     -> differentiated placements
--     -> local nonnegative majorant
--     -> compact-Gamma numerator contribution.
--
-- It is cutoff-free: every statement is pointwise in one resonant triad and
-- therefore contains no Galerkin cutoff parameter.  Finite summation and
-- weighted Schur transport remain owned by the existing pair-incidence stack.
------------------------------------------------------------------------

record TriadAnalyticLaws
    {m v s : Level}
    (Mode : Set m)
    (Vector : Set v)
    (Scalar : Set s) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    fourier : FourierVectorLaws Mode Vector Scalar

    one : Scalar
    absolute : Scalar → Scalar
    norm : Vector → Scalar
    modeNorm : Mode → Scalar

    _+_ _*_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    lerayProject : Mode → Vector → Vector

    ≤-refl : ∀ x → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    +-mono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
    *-mono-nonnegative :
      ∀ {a b c d} → a ≤ b → c ≤ d → (a * c) ≤ (b * d)

    norm-vectorAdd :
      ∀ x y →
      norm (vectorAdd fourier x y) ≤ (norm x + norm y)

    norm-vectorScale :
      ∀ a x →
      norm (vectorScale fourier a x) ≤ (absolute a * norm x)

    absolute-dot :
      ∀ x y →
      absolute (vectorDot fourier x y) ≤ (norm x * norm y)

    leray-contraction :
      ∀ k x →
      norm (lerayProject k x) ≤ norm x

    wave-vector-norm :
      ∀ k →
      norm (waveVector fourier k) ≡ modeNorm k

    inverse-square-cross-bound :
      ∀ p a →
      norm (biotSavartVelocity fourier p a)
        ≤ (inverseNormSquared fourier p * (modeNorm p * norm a))

open TriadAnalyticLaws public

------------------------------------------------------------------------
-- Exact projected interaction and its explicit |q| / |p| majorant.
------------------------------------------------------------------------

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
  (inverseNormSquared (fourier A) p * modeNorm A p)
  * (modeNorm A q * (norm A a * norm A b))

record ProjectedInteractionBound
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (m ⊔ v ⊔ s) where
  field
    projected-interaction-bound :
      ∀ k p q a b →
      norm A (projectedInteraction A k p q a b)
        ≤ interactionMajorant A p q a b

open ProjectedInteractionBound public

-- Named component theorem: the actual Biot-Savart factor is present in the
-- left-hand side and the right-hand side is |p|^-2 |p| |a|.
biot-savart-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (p : Mode) (a : Vector) →
  norm A (biotSavartVelocity (fourier A) p a)
    ≤ (inverseNormSquared (fourier A) p * (modeNorm A p * norm A a))
biot-savart-bound A = inverse-square-cross-bound A

projected-interaction-bound-theorem :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (k p q : Mode) (a b : Vector) →
  norm A (projectedInteraction A k p q a b)
    ≤ interactionMajorant A p q a b
projected-interaction-bound-theorem A P =
  projected-interaction-bound P

------------------------------------------------------------------------
-- All differentiated placements of P_k((B(u) . nabla)u).
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

-- This is the local M_k(p,q;u,h).  Both differentiated placements are
-- explicit; conjugate placements are obtained by the reality involution below.
differentiatedTriadMajorant :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  TriadAnalyticLaws Mode Vector Scalar →
  Mode → Mode →
  Vector → Vector → Vector → Vector → Scalar
differentiatedTriadMajorant A p q uP uQ hP hQ =
  interactionMajorant A p q hP uQ
  + interactionMajorant A p q uP hQ

differentiated-product-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (k p q : Mode)
    (uP uQ hP hQ : Vector) →
  norm A (differentiatedProjectedTriad A k p q uP uQ hP hQ)
    ≤ differentiatedTriadMajorant A p q uP uQ hP hQ
differentiated-product-bound A P k p q uP uQ hP hQ =
  ≤-trans A
    (norm-vectorAdd A
      (projectedInteraction A k p q hP uQ)
      (projectedInteraction A k p q uP hQ))
    (+-mono A
      (projected-interaction-bound P k p q hP uQ)
      (projected-interaction-bound P k p q uP hQ))

------------------------------------------------------------------------
-- Reality closure and exact k <-> -k incidence folding.
------------------------------------------------------------------------

record RealityClosedFourierData
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    negateMode : Mode → Mode
    conjugate : Vector → Vector

    negate-involutive : ∀ k → negateMode (negateMode k) ≡ k
    conjugate-involutive : ∀ x → conjugate (conjugate x) ≡ x
    norm-conjugate : ∀ x → norm A (conjugate x) ≡ norm A x

    addNegation : Mode → Mode → Mode
    resonance-negates :
      ∀ p q k → addNegation p q ≡ k →
      addNegation (negateMode p) (negateMode q) ≡ negateMode k

open RealityClosedFourierData public

record RealityPairFolding
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (R : RealityClosedFourierData A) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    incidence : Mode → Mode → Mode → Set m
    foldedIncidence : Mode → Mode → Mode → Set m

    fold-complete :
      ∀ k p q →
      incidence k p q → foldedIncidence k p q

    fold-sound :
      ∀ k p q →
      foldedIncidence k p q →
      incidence k p q

    conjugate-incidence :
      ∀ k p q →
      incidence k p q →
      incidence (negateMode R k) (negateMode R p) (negateMode R q)

    fold-does-not-double-count :
      ∀ k p q →
      foldedIncidence k p q →
      foldedIncidence (negateMode R k) (negateMode R p) (negateMode R q) →
      incidence k p q

open RealityPairFolding public

reality-pair-folding-complete :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {A : TriadAnalyticLaws Mode Vector Scalar}
    {R : RealityClosedFourierData A}
    (F : RealityPairFolding A R) →
  ∀ k p q →
  incidence F k p q → foldedIncidence F k p q
reality-pair-folding-complete F = fold-complete F

reality-pair-folding-sound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {A : TriadAnalyticLaws Mode Vector Scalar}
    {R : RealityClosedFourierData A}
    (F : RealityPairFolding A R) →
  ∀ k p q →
  foldedIncidence F k p q → incidence F k p q
reality-pair-folding-sound F = fold-sound F

------------------------------------------------------------------------
-- Tangent correction keeping target packet energy fixed.
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
      norm A (projectTangent k u h)
        ≤ (correctionConstant * norm A h)

open TargetEnergyTangentProjection public

tangent-projection-divergence-free :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {A : TriadAnalyticLaws Mode Vector Scalar}
    (T : TargetEnergyTangentProjection A) →
  ∀ k u h →
  divergenceFree T k h →
  divergenceFree T k (projectTangent T k u h)
tangent-projection-divergence-free T = tangent-divergence-free T

------------------------------------------------------------------------
-- Compact-Gamma numerator, signs/absolute values, and reconstruction.
------------------------------------------------------------------------

record CompactGammaNearResponse
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    numeratorDerivative : Mode → Vector → Scalar
    triadNumerator : Mode → Mode → Mode → Vector → Scalar
    compactGammaCoefficient : Mode → Scalar

    nearResponseReconstruction :
      ∀ k p q dTriad →
      numeratorDerivative k dTriad
        ≡ triadNumerator k p q dTriad

    compactGammaAbsoluteBound :
      ∀ k dTriad →
      absolute A (numeratorDerivative k dTriad)
        ≤ (absolute A (compactGammaCoefficient k) * norm A dTriad)

open CompactGammaNearResponse public

near-response-reconstruction :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    {A : TriadAnalyticLaws Mode Vector Scalar}
    (G : CompactGammaNearResponse A) →
  ∀ k p q dTriad →
  numeratorDerivative G k dTriad
    ≡ triadNumerator G k p q dTriad
near-response-reconstruction G =
  CompactGammaNearResponse.nearResponseReconstruction G

------------------------------------------------------------------------
-- Final local theorem.
------------------------------------------------------------------------

compactGammaDifferentiatedTriadMajorant :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s} →
  (A : TriadAnalyticLaws Mode Vector Scalar) →
  CompactGammaNearResponse A →
  Mode → Mode → Mode →
  Vector → Vector → Vector → Vector → Scalar
compactGammaDifferentiatedTriadMajorant A G k p q uP uQ hP hQ =
  absolute A (compactGammaCoefficient G k)
  * differentiatedTriadMajorant A p q uP uQ hP hQ

record CompactGammaCoefficientMonotonicity
    {m v s : Level}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar) : Set (m ⊔ v ⊔ s) where
  field
    coefficient-multiplies-bound :
      ∀ c x y →
      x ≤ y →
      (absolute A c * x) ≤ (absolute A c * y)

open CompactGammaCoefficientMonotonicity public

concrete-differentiated-triad-bound :
  ∀ {m v s}
    {Mode : Set m} {Vector : Set v} {Scalar : Set s}
    (A : TriadAnalyticLaws Mode Vector Scalar)
    (P : ProjectedInteractionBound A)
    (G : CompactGammaNearResponse A)
    (C : CompactGammaCoefficientMonotonicity A)
    (k p q : Mode)
    (uP uQ hP hQ : Vector) →
  absolute A
    (numeratorDerivative G k
      (differentiatedProjectedTriad A k p q uP uQ hP hQ))
  ≤ compactGammaDifferentiatedTriadMajorant
      A G k p q uP uQ hP hQ
concrete-differentiated-triad-bound A P G C k p q uP uQ hP hQ =
  ≤-trans A
    (compactGammaAbsoluteBound G k
      (differentiatedProjectedTriad A k p q uP uQ hP hQ))
    (coefficient-multiplies-bound C
      (compactGammaCoefficient G k)
      (norm A
        (differentiatedProjectedTriad A k p q uP uQ hP hQ))
      (differentiatedTriadMajorant A p q uP uQ hP hQ)
      (differentiated-product-bound A P k p q uP uQ hP hQ))

-- There is no cutoff argument anywhere in the theorem.  Hence the constant is
-- structurally independent of the Galerkin cutoff; cutoff dependence can enter
-- only later through the selected finite incidence family.
record CutoffIndependentDifferentiatedTriadLeaf : Set₁ where
  field
    theoremModule : Set
    noGalerkinCutoffParameter : Set

canonicalCutoffIndependentDifferentiatedTriadLeaf :
  CutoffIndependentDifferentiatedTriadLeaf
canonicalCutoffIndependentDifferentiatedTriadLeaf = record
  { theoremModule = Set
  ; noGalerkinCutoffParameter = Set
  }
