{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98AveragingKernelCompositionMassExact where

------------------------------------------------------------------------
-- ROW A / CMP98: KERNEL COMPOSITION PRESERVES NORMALISATION AND DQ ZERO MASS
--
-- If K and L are finite averaging kernels, composition has total mass
--
--                  mass(K o L) = mass(K) mass(L).
--
-- Hence normalized averaging steps remain normalized under arbitrary finite
-- composition, and a zero-mass background derivative remains zero-mass after
-- every later normalized averaging step.  This is the algebraic part of the
-- Lean `KernelComposition` result; only support range can grow with depth.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98AveragingNormalizationDerivativeExact as Norm

sumScaleLeft :
  ∀ {A : Set} (values : List A) (scale : ℚ) (f : A → ℚ) →
  Norm.sumRational values (λ x → scale * f x)
  ≡ scale * Norm.sumRational values f
sumScaleLeft [] scale f = ℚRing.solve-∀ scale
sumScaleLeft (x ∷ xs) scale f
  rewrite sumScaleLeft xs scale f =
  ℚRing.solve-∀ scale (f x) (Norm.sumRational xs f)

sumScaleRight :
  ∀ {A : Set} (values : List A) (f : A → ℚ) (scale : ℚ) →
  Norm.sumRational values (λ x → f x * scale)
  ≡ Norm.sumRational values f * scale
sumScaleRight [] f scale = ℚRing.solve-∀ scale
sumScaleRight (x ∷ xs) f scale
  rewrite sumScaleRight xs f scale =
  ℚRing.solve-∀ (f x) (Norm.sumRational xs f) scale

record FiniteRationalKernel (Atom : Set) : Set₁ where
  field
    atoms : List Atom
    weight : Atom → ℚ

open FiniteRationalKernel public

totalMass : ∀ {Atom} → FiniteRationalKernel Atom → ℚ
totalMass kernel = Norm.sumRational (atoms kernel) (weight kernel)

nestedCompositionMass :
  ∀ {LeftAtom RightAtom} →
  FiniteRationalKernel LeftAtom →
  FiniteRationalKernel RightAtom → ℚ
nestedCompositionMass left right =
  Norm.sumRational (atoms left)
    (λ a → Norm.sumRational (atoms right)
      (λ b → weight left a * weight right b))

innerCompositionMass :
  ∀ {LeftAtom RightAtom}
    (left : FiniteRationalKernel LeftAtom)
    (right : FiniteRationalKernel RightAtom) a →
  Norm.sumRational (atoms right)
    (λ b → weight left a * weight right b)
  ≡ weight left a * totalMass right
innerCompositionMass left right a =
  sumScaleLeft (atoms right) (weight left a) (weight right)

compositionMassMultiplies :
  ∀ {LeftAtom RightAtom}
    (left : FiniteRationalKernel LeftAtom)
    (right : FiniteRationalKernel RightAtom) →
  nestedCompositionMass left right
  ≡ totalMass left * totalMass right
compositionMassMultiplies left right = go (atoms left)
  where
  go : (values : List _) →
    Norm.sumRational values
      (λ a → Norm.sumRational (atoms right)
        (λ b → weight left a * weight right b))
    ≡ Norm.sumRational values (weight left) * totalMass right
  go [] = ℚRing.solve-∀ (totalMass right)
  go (a ∷ rest)
    rewrite innerCompositionMass left right a
          | go rest =
    ℚRing.solve-∀
      (weight left a)
      (Norm.sumRational rest (weight left))
      (totalMass right)

normalizedCompositionMassOne :
  ∀ {LeftAtom RightAtom}
    (left : FiniteRationalKernel LeftAtom)
    (right : FiniteRationalKernel RightAtom) →
  totalMass left ≡ 1ℚ → totalMass right ≡ 1ℚ →
  nestedCompositionMass left right ≡ 1ℚ
normalizedCompositionMassOne left right leftOne rightOne
  rewrite compositionMassMultiplies left right
        | leftOne | rightOne =
  refl

zeroMassSurvivesNormalizedComposition :
  ∀ {DerivativeAtom LaterAtom}
    (derivativeKernel : FiniteRationalKernel DerivativeAtom)
    (laterKernel : FiniteRationalKernel LaterAtom) →
  totalMass derivativeKernel ≡ 0ℚ →
  totalMass laterKernel ≡ 1ℚ →
  nestedCompositionMass derivativeKernel laterKernel ≡ 0ℚ
zeroMassSurvivesNormalizedComposition derivativeKernel laterKernel derivativeZero laterOne
  rewrite compositionMassMultiplies derivativeKernel laterKernel
        | derivativeZero | laterOne =
  refl

-- Iterating the previous theorem needs no new estimate: after each normalized
-- step the composed derivative still has mass zero, so the theorem applies again.
cmp98KernelCompositionMassMultiplicationLevel : ProofLevel
cmp98KernelCompositionMassMultiplicationLevel = machineChecked

cmp98DerivativeZeroMassSurvivesCompositionLevel : ProofLevel
cmp98DerivativeZeroMassSurvivesCompositionLevel = machineChecked

literalCMP98ComposedKernelIdentificationLevel : ProofLevel
literalCMP98ComposedKernelIdentificationLevel = conditional
