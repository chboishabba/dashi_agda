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
-- composition with any number of later normalized steps:
--
--                  0 * 1 * ... * 1 = 0.
--
-- This is the algebraic part of the Lean `KernelComposition` result.  It removes
-- RG-depth dependence from the mass/cancellation hypothesis: only support range
-- may grow with the number of composed steps.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98AveragingNormalizationDerivativeExact as Norm

sumScale :
  ∀ {A : Set} (values : List A) (scale : ℚ) (f : A → ℚ) →
  Norm.sumRational values (λ x → scale * f x)
  ≡ scale * Norm.sumRational values f
sumScale [] scale f = symZero
  where
  symZero : 0ℚ ≡ scale * 0ℚ
  symZero = Agda.Builtin.Equality.refl
sumScale (x ∷ xs) scale f =
  trans
    (cong (scale * f x +_) (sumScale xs scale f))
    (ℚP.*-distribˡ-+ scale (f x) (Norm.sumRational xs f))

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
  sumScale (atoms right) (weight left a) (weight right)

compositionMassMultiplies :
  ∀ {LeftAtom RightAtom}
    (left : FiniteRationalKernel LeftAtom)
    (right : FiniteRationalKernel RightAtom) →
  nestedCompositionMass left right
  ≡ totalMass left * totalMass right
compositionMassMultiplies left right =
  trans
    (sumCong (atoms left))
    (sumScale (atoms left) (totalMass right) (weight left) |> commute)
  where
  sumCong : (values : List _) →
    Norm.sumRational values
      (λ a → Norm.sumRational (atoms right)
        (λ b → weight left a * weight right b))
    ≡ Norm.sumRational values
      (λ a → weight left a * totalMass right)
  sumCong [] = refl
  sumCong (a ∷ rest) =
    cong₂ _+_ (innerCompositionMass left right a) (sumCong rest)

  commute :
    Norm.sumRational (atoms left)
      (λ a → totalMass right * weight left a)
    ≡ totalMass left * totalMass right
  commute =
    trans
      (sumCommute (atoms left))
      (ℚP.*-comm (totalMass right) (totalMass left))
    where
    sumCommute : (values : List _) →
      Norm.sumRational values
        (λ a → totalMass right * weight left a)
      ≡ Norm.sumRational values
        (λ a → weight left a * totalMass right)
    sumCommute [] = refl
    sumCommute (a ∷ rest) =
      cong₂ _+_ (ℚP.*-comm (totalMass right) (weight left a)) (sumCommute rest)

-- Small helper replacing pipeline syntax in the theorem above.
infixl 0 _|>_
_|>_ : ∀ {A B : Set} → A → (A → B) → B
value |> f = f value

normalizedCompositionMassOne :
  ∀ {LeftAtom RightAtom}
    (left : FiniteRationalKernel LeftAtom)
    (right : FiniteRationalKernel RightAtom) →
  totalMass left ≡ 1ℚ → totalMass right ≡ 1ℚ →
  nestedCompositionMass left right ≡ 1ℚ
normalizedCompositionMassOne left right leftOne rightOne =
  trans
    (compositionMassMultiplies left right)
    (trans
      (cong₂ _*_ leftOne rightOne)
      (ℚP.*-identityˡ 1ℚ))

zeroMassSurvivesNormalizedComposition :
  ∀ {DerivativeAtom LaterAtom}
    (derivativeKernel : FiniteRationalKernel DerivativeAtom)
    (laterKernel : FiniteRationalKernel LaterAtom) →
  totalMass derivativeKernel ≡ 0ℚ →
  totalMass laterKernel ≡ 1ℚ →
  nestedCompositionMass derivativeKernel laterKernel ≡ 0ℚ
zeroMassSurvivesNormalizedComposition derivativeKernel laterKernel derivativeZero laterOne =
  trans
    (compositionMassMultiplies derivativeKernel laterKernel)
    (trans
      (cong₂ _*_ derivativeZero laterOne)
      refl)

massProduct : List ℚ → ℚ
massProduct [] = 1ℚ
massProduct (m ∷ ms) = m * massProduct ms

allNormalizedProductOne :
  (masses : List ℚ) →
  (∀ mass → member mass masses → mass ≡ 1ℚ) →
  massProduct masses ≡ 1ℚ
allNormalizedProductOne [] allOne = refl
allNormalizedProductOne (m ∷ ms) allOne =
  trans
    (cong₂ _*_
      (allOne m here)
      (allNormalizedProductOne ms (λ mass proof → allOne mass (there proof))))
    (ℚP.*-identityˡ 1ℚ)
  where
  data member (x : ℚ) : List ℚ → Set where
    here : ∀ {xs} → member x (x ∷ xs)
    there : ∀ {y xs} → member x xs → member x (y ∷ xs)

zeroMassTimesAnyProduct :
  (masses : List ℚ) → 0ℚ * massProduct masses ≡ 0ℚ
zeroMassTimesAnyProduct masses = refl

cmp98KernelCompositionMassMultiplicationLevel : ProofLevel
cmp98KernelCompositionMassMultiplicationLevel = machineChecked

cmp98DerivativeZeroMassSurvivesCompositionLevel : ProofLevel
cmp98DerivativeZeroMassSurvivesCompositionLevel = machineChecked

-- Physical/source seam: identify each later RG averaging step with a normalized
-- finite CMP98/CMP99 kernel.  No extra zero-mass assumption may then be added for
-- the composed Q' object; it follows from the initial derivative cancellation.
literalCMP98ComposedKernelIdentificationLevel : ProofLevel
literalCMP98ComposedKernelIdentificationLevel = conditional
