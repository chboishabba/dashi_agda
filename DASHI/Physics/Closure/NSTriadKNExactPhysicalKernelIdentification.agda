module DASHI.Physics.Closure.NSTriadKNExactPhysicalKernelIdentification where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula

------------------------------------------------------------------------
-- Exact list-level physical/code kernel identification.
--
-- Once a code fibre is proved to be exactly the image of its physical fibre,
-- and the encoding preserves the one canonical physical weight, equality of
-- the finite kernels is derived by recursion.  No eigenvalue estimate enters
-- this layer.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

weightedListSumMap :
  ∀ {Physical Code : Set}
    (encode : Physical → Code)
    (physicalWeight : Physical → Nat)
    (codeWeight : Code → Nat) →
  ((x : Physical) → codeWeight (encode x) ≡ physicalWeight x) →
  (xs : List Physical) →
  KernelFormula.weightedListSum codeWeight (mapList encode xs)
  ≡ KernelFormula.weightedListSum physicalWeight xs
weightedListSumMap encode physicalWeight codeWeight preserves [] = refl
weightedListSumMap encode physicalWeight codeWeight preserves (x ∷ xs) =
  cong₂ _+_
    (preserves x)
    (weightedListSumMap encode physicalWeight codeWeight preserves xs)
  where
  cong₂ :
    ∀ {A B C : Set} (f : A → B → C)
      {a a′ : A} {b b′ : B} →
    a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
  cong₂ f refl refl = refl

record ExactPhysicalKernelIdentificationInputs : Set₁ where
  constructor exact-physical-kernel-inputs
  field
    Index : Set
    PhysicalIncidence CodeIncidence : Set

    encode : PhysicalIncidence → CodeIncidence

    physicalWeight : PhysicalIncidence → Nat
    codeWeight : CodeIncidence → Nat
    encodePreservesWeight :
      (τ : PhysicalIncidence) →
      codeWeight (encode τ) ≡ physicalWeight τ

    physicalFiber :
      Index → Index → List PhysicalIncidence
    codeFiber :
      Index → Index → List CodeIncidence

    codeFiberIsEncodedPhysicalFiber :
      (i j : Index) →
      codeFiber i j ≡ mapList encode (physicalFiber i j)

open ExactPhysicalKernelIdentificationInputs public

physicalKernel :
  (inputs : ExactPhysicalKernelIdentificationInputs) →
  Index inputs → Index inputs → Nat
physicalKernel inputs i j =
  KernelFormula.weightedListSum
    (physicalWeight inputs)
    (physicalFiber inputs i j)

codeKernel :
  (inputs : ExactPhysicalKernelIdentificationInputs) →
  Index inputs → Index inputs → Nat
codeKernel inputs i j =
  KernelFormula.weightedListSum
    (codeWeight inputs)
    (codeFiber inputs i j)

exactPhysicalKernelIdentification :
  (inputs : ExactPhysicalKernelIdentificationInputs) →
  (i j : Index inputs) →
  codeKernel inputs i j ≡ physicalKernel inputs i j
exactPhysicalKernelIdentification inputs i j =
  trans
    (cong
      (KernelFormula.weightedListSum (codeWeight inputs))
      (codeFiberIsEncodedPhysicalFiber inputs i j))
    (weightedListSumMap
      (encode inputs)
      (physicalWeight inputs)
      (codeWeight inputs)
      (encodePreservesWeight inputs)
      (physicalFiber inputs i j))

record PhysicalFiberRepresentationLaws
    (inputs : ExactPhysicalKernelIdentificationInputs) : Set₁ where
  field
    physicalSource physicalTarget :
      PhysicalIncidence inputs → Index inputs
    codeSource codeTarget :
      CodeIncidence inputs → Index inputs

    encodePreservesSource :
      (τ : PhysicalIncidence inputs) →
      codeSource (encode inputs τ) ≡ physicalSource τ
    encodePreservesTarget :
      (τ : PhysicalIncidence inputs) →
      codeTarget (encode inputs τ) ≡ physicalTarget τ

    PhysicalDuplicateFree :
      List (PhysicalIncidence inputs) → Set
    CodeDuplicateFree :
      List (CodeIncidence inputs) → Set

    physicalFiberDuplicateFree :
      (i j : Index inputs) →
      PhysicalDuplicateFree (physicalFiber inputs i j)
    codeFiberDuplicateFree :
      (i j : Index inputs) →
      CodeDuplicateFree (codeFiber inputs i j)

open PhysicalFiberRepresentationLaws public

exactPhysicalKernelIdentificationReductionImplemented : Bool
exactPhysicalKernelIdentificationReductionImplemented = true

exactPhysicalKernelIdentificationReductionImplementedIsTrue :
  exactPhysicalKernelIdentificationReductionImplemented ≡ true
exactPhysicalKernelIdentificationReductionImplementedIsTrue = refl

physicalCodeFiberImageTheoremInhabited : Bool
physicalCodeFiberImageTheoremInhabited = false

physicalCodeFiberImageTheoremInhabitedIsFalse :
  physicalCodeFiberImageTheoremInhabited ≡ false
physicalCodeFiberImageTheoremInhabitedIsFalse = refl
