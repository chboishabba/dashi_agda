module DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact where

------------------------------------------------------------------------
-- EXPLICIT F3-LINEAR OPERATIONS ON THE CANONICAL TRIADIC KERNELS
--
-- Coordinate convention:
--   zer = 0, pos = 1, neg = 2 = -1  in F3.
--
-- This owner pays the additive/scalar operation surface directly on the
-- existing TriadicPAdicCodec.Kernel d carrier.  A chosen extension-field
-- multiplication for d=4,5,6 is runtime-certified separately; it is not
-- silently promoted to an intrinsic pre-existing DASHI multiplication.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Codec.TriadicPAdicCodec using
  (Kernel; []ᵥ; _∷ᵥ_; invertKernel)

infixl 6 _⊕₃_
infixl 7 _⊗₃_

_⊕₃_ : Trit → Trit → Trit
neg ⊕₃ neg = pos
neg ⊕₃ zer = neg
neg ⊕₃ pos = zer
zer ⊕₃ neg = neg
zer ⊕₃ zer = zer
zer ⊕₃ pos = pos
pos ⊕₃ neg = zer
pos ⊕₃ zer = pos
pos ⊕₃ pos = neg

_⊗₃_ : Trit → Trit → Trit
neg ⊗₃ neg = pos
neg ⊗₃ zer = zer
neg ⊗₃ pos = neg
zer ⊗₃ neg = zer
zer ⊗₃ zer = zer
zer ⊗₃ pos = zer
pos ⊗₃ neg = neg
pos ⊗₃ zer = zer
pos ⊗₃ pos = pos

additiveZeroLeft : (x : Trit) → zer ⊕₃ x ≡ x
additiveZeroLeft neg = refl
additiveZeroLeft zer = refl
additiveZeroLeft pos = refl

additiveZeroRight : (x : Trit) → x ⊕₃ zer ≡ x
additiveZeroRight neg = refl
additiveZeroRight zer = refl
additiveZeroRight pos = refl

additiveInverse : (x : Trit) → x ⊕₃ inv x ≡ zer
additiveInverse neg = refl
additiveInverse zer = refl
additiveInverse pos = refl

multiplicativeOneLeft : (x : Trit) → pos ⊗₃ x ≡ x
multiplicativeOneLeft neg = refl
multiplicativeOneLeft zer = refl
multiplicativeOneLeft pos = refl

multiplicativeOneRight : (x : Trit) → x ⊗₃ pos ≡ x
multiplicativeOneRight neg = refl
multiplicativeOneRight zer = refl
multiplicativeOneRight pos = refl

minusOneActsByInverse : (x : Trit) → neg ⊗₃ x ≡ inv x
minusOneActsByInverse neg = refl
minusOneActsByInverse zer = refl
minusOneActsByInverse pos = refl

zeroKernel : {d : Nat} → Kernel d
zeroKernel {zero} = []ᵥ
zeroKernel {suc d} = zer ∷ᵥ zeroKernel

addKernel : {d : Nat} → Kernel d → Kernel d → Kernel d
addKernel []ᵥ []ᵥ = []ᵥ
addKernel (x ∷ᵥ xs) (y ∷ᵥ ys) = (x ⊕₃ y) ∷ᵥ addKernel xs ys

scaleKernel : {d : Nat} → Trit → Kernel d → Kernel d
scaleKernel scalar []ᵥ = []ᵥ
scaleKernel scalar (x ∷ᵥ xs) = (scalar ⊗₃ x) ∷ᵥ scaleKernel scalar xs

addKernelZeroLeft : {d : Nat} → (x : Kernel d) → addKernel zeroKernel x ≡ x
addKernelZeroLeft []ᵥ = refl
addKernelZeroLeft (x ∷ᵥ xs)
  rewrite additiveZeroLeft x | addKernelZeroLeft xs = refl

addKernelZeroRight : {d : Nat} → (x : Kernel d) → addKernel x zeroKernel ≡ x
addKernelZeroRight []ᵥ = refl
addKernelZeroRight (x ∷ᵥ xs)
  rewrite additiveZeroRight x | addKernelZeroRight xs = refl

scaleOneIdentity : {d : Nat} → (x : Kernel d) → scaleKernel pos x ≡ x
scaleOneIdentity []ᵥ = refl
scaleOneIdentity (x ∷ᵥ xs)
  rewrite multiplicativeOneLeft x | scaleOneIdentity xs = refl

scaleMinusOneIsCodecInversion :
  {d : Nat} → (x : Kernel d) → scaleKernel neg x ≡ invertKernel x
scaleMinusOneIsCodecInversion []ᵥ = refl
scaleMinusOneIsCodecInversion (x ∷ᵥ xs)
  rewrite minusOneActsByInverse x | scaleMinusOneIsCodecInversion xs = refl

Kernel4 Kernel5 Kernel6 : Set
Kernel4 = Kernel 4
Kernel5 = Kernel 5
Kernel6 = Kernel 6

record KernelF3LinearBoundary : Set where
  constructor kernel-f3-linear-boundary
  field
    coordinateF3OperationsSourceWritten : Bool
    kernelAdditionSourceWritten : Bool
    scalarActionSourceWritten : Bool
    zeroAndOneLawsPaid : Bool
    existingKernelInversionIsMinusOneScalar : Bool
    fullVectorSpaceLawBundlePackaged : Bool
    chosenExtensionMultiplicationIntrinsicToPriorRepo : Bool
    fullFiniteFieldRecognitionClaimedHere : Bool

canonicalKernelF3LinearBoundary : KernelF3LinearBoundary
canonicalKernelF3LinearBoundary =
  kernel-f3-linear-boundary
    true true true true true
    false false false
