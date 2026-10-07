module DASHI.Moonshine.OggSSPTriadicKernelF3LinearExact where

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

multiplicativeZeroRight : (x : Trit) → x ⊗₃ zer ≡ zer
multiplicativeZeroRight neg = refl
multiplicativeZeroRight zer = refl
multiplicativeZeroRight pos = refl

minusOneActsByInverse : (x : Trit) → neg ⊗₃ x ≡ inv x
minusOneActsByInverse neg = refl
minusOneActsByInverse zer = refl
minusOneActsByInverse pos = refl

addComm : (a b : Trit) → a ⊕₃ b ≡ b ⊕₃ a
addComm neg neg = refl
addComm neg zer = refl
addComm neg pos = refl
addComm zer neg = refl
addComm zer zer = refl
addComm zer pos = refl
addComm pos neg = refl
addComm pos zer = refl
addComm pos pos = refl

addAssoc : (a b c : Trit) → (a ⊕₃ b) ⊕₃ c ≡ a ⊕₃ (b ⊕₃ c)
addAssoc neg neg neg = refl
addAssoc neg neg zer = refl
addAssoc neg neg pos = refl
addAssoc neg zer neg = refl
addAssoc neg zer zer = refl
addAssoc neg zer pos = refl
addAssoc neg pos neg = refl
addAssoc neg pos zer = refl
addAssoc neg pos pos = refl
addAssoc zer neg neg = refl
addAssoc zer neg zer = refl
addAssoc zer neg pos = refl
addAssoc zer zer neg = refl
addAssoc zer zer zer = refl
addAssoc zer zer pos = refl
addAssoc zer pos neg = refl
addAssoc zer pos zer = refl
addAssoc zer pos pos = refl
addAssoc pos neg neg = refl
addAssoc pos neg zer = refl
addAssoc pos neg pos = refl
addAssoc pos zer neg = refl
addAssoc pos zer zer = refl
addAssoc pos zer pos = refl
addAssoc pos pos neg = refl
addAssoc pos pos zer = refl
addAssoc pos pos pos = refl

mulComm : (a b : Trit) → a ⊗₃ b ≡ b ⊗₃ a
mulComm neg neg = refl
mulComm neg zer = refl
mulComm neg pos = refl
mulComm zer neg = refl
mulComm zer zer = refl
mulComm zer pos = refl
mulComm pos neg = refl
mulComm pos zer = refl
mulComm pos pos = refl

mulAssoc : (a b c : Trit) → (a ⊗₃ b) ⊗₃ c ≡ a ⊗₃ (b ⊗₃ c)
mulAssoc neg neg neg = refl
mulAssoc neg neg zer = refl
mulAssoc neg neg pos = refl
mulAssoc neg zer neg = refl
mulAssoc neg zer zer = refl
mulAssoc neg zer pos = refl
mulAssoc neg pos neg = refl
mulAssoc neg pos zer = refl
mulAssoc neg pos pos = refl
mulAssoc zer neg neg = refl
mulAssoc zer neg zer = refl
mulAssoc zer neg pos = refl
mulAssoc zer zer neg = refl
mulAssoc zer zer zer = refl
mulAssoc zer zer pos = refl
mulAssoc zer pos neg = refl
mulAssoc zer pos zer = refl
mulAssoc zer pos pos = refl
mulAssoc pos neg neg = refl
mulAssoc pos neg zer = refl
mulAssoc pos neg pos = refl
mulAssoc pos zer neg = refl
mulAssoc pos zer zer = refl
mulAssoc pos zer pos = refl
mulAssoc pos pos neg = refl
mulAssoc pos pos zer = refl
mulAssoc pos pos pos = refl

leftDistrib : (a b c : Trit) → a ⊗₃ (b ⊕₃ c) ≡ (a ⊗₃ b) ⊕₃ (a ⊗₃ c)
leftDistrib neg neg neg = refl
leftDistrib neg neg zer = refl
leftDistrib neg neg pos = refl
leftDistrib neg zer neg = refl
leftDistrib neg zer zer = refl
leftDistrib neg zer pos = refl
leftDistrib neg pos neg = refl
leftDistrib neg pos zer = refl
leftDistrib neg pos pos = refl
leftDistrib zer neg neg = refl
leftDistrib zer neg zer = refl
leftDistrib zer neg pos = refl
leftDistrib zer zer neg = refl
leftDistrib zer zer zer = refl
leftDistrib zer zer pos = refl
leftDistrib zer pos neg = refl
leftDistrib zer pos zer = refl
leftDistrib zer pos pos = refl
leftDistrib pos neg neg = refl
leftDistrib pos neg zer = refl
leftDistrib pos neg pos = refl
leftDistrib pos zer neg = refl
leftDistrib pos zer zer = refl
leftDistrib pos zer pos = refl
leftDistrib pos pos neg = refl
leftDistrib pos pos zer = refl
leftDistrib pos pos pos = refl

rightDistrib : (a b c : Trit) → (a ⊕₃ b) ⊗₃ c ≡ (a ⊗₃ c) ⊕₃ (b ⊗₃ c)
rightDistrib neg neg neg = refl
rightDistrib neg neg zer = refl
rightDistrib neg neg pos = refl
rightDistrib neg zer neg = refl
rightDistrib neg zer zer = refl
rightDistrib neg zer pos = refl
rightDistrib neg pos neg = refl
rightDistrib neg pos zer = refl
rightDistrib neg pos pos = refl
rightDistrib zer neg neg = refl
rightDistrib zer neg zer = refl
rightDistrib zer neg pos = refl
rightDistrib zer zer neg = refl
rightDistrib zer zer zer = refl
rightDistrib zer zer pos = refl
rightDistrib zer pos neg = refl
rightDistrib zer pos zer = refl
rightDistrib zer pos pos = refl
rightDistrib pos neg neg = refl
rightDistrib pos neg zer = refl
rightDistrib pos neg pos = refl
rightDistrib pos zer neg = refl
rightDistrib pos zer zer = refl
rightDistrib pos zer pos = refl
rightDistrib pos pos neg = refl
rightDistrib pos pos zer = refl
rightDistrib pos pos pos = refl

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

addKernelComm : {d : Nat} → (x y : Kernel d) → addKernel x y ≡ addKernel y x
addKernelComm []ᵥ []ᵥ = refl
addKernelComm (x ∷ᵥ xs) (y ∷ᵥ ys)
  rewrite addComm x y | addKernelComm xs ys = refl

addKernelAssoc :
  {d : Nat} → (x y z : Kernel d) →
  addKernel (addKernel x y) z ≡ addKernel x (addKernel y z)
addKernelAssoc []ᵥ []ᵥ []ᵥ = refl
addKernelAssoc (x ∷ᵥ xs) (y ∷ᵥ ys) (z ∷ᵥ zs)
  rewrite addAssoc x y z | addKernelAssoc xs ys zs = refl

addKernelInverse :
  {d : Nat} → (x : Kernel d) → addKernel x (invertKernel x) ≡ zeroKernel
addKernelInverse []ᵥ = refl
addKernelInverse (x ∷ᵥ xs)
  rewrite additiveInverse x | addKernelInverse xs = refl

scaleOneIdentity : {d : Nat} → (x : Kernel d) → scaleKernel pos x ≡ x
scaleOneIdentity []ᵥ = refl
scaleOneIdentity (x ∷ᵥ xs)
  rewrite multiplicativeOneLeft x | scaleOneIdentity xs = refl

scaleZeroVector : {d : Nat} → (a : Trit) → scaleKernel a zeroKernel ≡ zeroKernel
scaleZeroVector {zero} a = refl
scaleZeroVector {suc d} a
  rewrite multiplicativeZeroRight a | scaleZeroVector {d} a = refl

scaleZeroScalar : {d : Nat} → (x : Kernel d) → scaleKernel zer x ≡ zeroKernel
scaleZeroScalar []ᵥ = refl
scaleZeroScalar (x ∷ᵥ xs)
  rewrite scaleZeroScalar xs = refl

scaleDistributesVectorAdd :
  {d : Nat} → (a : Trit) → (x y : Kernel d) →
  scaleKernel a (addKernel x y)
  ≡ addKernel (scaleKernel a x) (scaleKernel a y)
scaleDistributesVectorAdd a []ᵥ []ᵥ = refl
scaleDistributesVectorAdd a (x ∷ᵥ xs) (y ∷ᵥ ys)
  rewrite leftDistrib a x y | scaleDistributesVectorAdd a xs ys = refl

scaleDistributesScalarAdd :
  {d : Nat} → (a b : Trit) → (x : Kernel d) →
  scaleKernel (a ⊕₃ b) x
  ≡ addKernel (scaleKernel a x) (scaleKernel b x)
scaleDistributesScalarAdd a b []ᵥ = refl
scaleDistributesScalarAdd a b (x ∷ᵥ xs)
  rewrite rightDistrib a b x | scaleDistributesScalarAdd a b xs = refl

scaleAssociates :
  {d : Nat} → (a b : Trit) → (x : Kernel d) →
  scaleKernel (a ⊗₃ b) x ≡ scaleKernel a (scaleKernel b x)
scaleAssociates a b []ᵥ = refl
scaleAssociates a b (x ∷ᵥ xs)
  rewrite mulAssoc a b x | scaleAssociates a b xs = refl

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
    scalarFieldLawsPaid : Bool
    kernelAdditionSourceWritten : Bool
    scalarActionSourceWritten : Bool
    vectorSpaceLawBundlePaid : Bool
    existingKernelInversionIsMinusOneScalar : Bool
    chosenExtensionMultiplicationIntrinsicToPriorRepo : Bool
    fullFiniteFieldRecognitionClaimedHere : Bool

canonicalKernelF3LinearBoundary : KernelF3LinearBoundary
canonicalKernelF3LinearBoundary =
  kernel-f3-linear-boundary
    true true true true true true
    false false
