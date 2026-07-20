module DASHI.Foundations.FiniteAdmissibleCoding where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

------------------------------------------------------------------------
-- The selectable controls at a state are controls paired with proofs of
-- admissibility.  A finite code is an explicit rank/unrank equivalence with
-- this proof-carrying set; it does not merely assert that one branch exists.

SelectedControl : ∀ {D} →
  ITD.AdmissibleControls D → ITD.State D → Set
SelectedControl {D} A s =
  Σ (ITD.Control D) (λ u → ITD.Admissible A s u)

record FiniteAdmissibleCode
  (D : ITD.InvolutiveDynamics)
  (A : ITD.AdmissibleControls D)
  (s : ITD.State D) : Set₁ where
  field
    Code : Set
    encode : SelectedControl A s → Code
    decode : Code → SelectedControl A s
    decode-encode : ∀ choice → decode (encode choice) ≡ choice
    encode-decode : ∀ code → encode (decode code) ≡ code

    branchCount : Nat
    codeBits : Code → Nat

open FiniteAdmissibleCode public

selectedControl : ∀ {D A s} →
  FiniteAdmissibleCode D A s → Code (FiniteAdmissibleCode D A s) →
  ITD.Control D
selectedControl C code = fst (decode C code)

selectedIsAdmissible : ∀ {D A s}
  (C : FiniteAdmissibleCode D A s)
  (code : Code C) →
  ITD.Admissible A s (selectedControl C code)
selectedIsAdmissible C code = snd (decode C code)

losslessControlRoundtrip : ∀ {D A s}
  (C : FiniteAdmissibleCode D A s)
  (choice : SelectedControl A s) →
  decode C (encode C choice) ≡ choice
losslessControlRoundtrip C = decode-encode C

------------------------------------------------------------------------
-- A branch stream accumulates the exact code costs selected at successive
-- states.  Its capacity/cost is derived from the codes, not from a primitive
-- binary alphabet.

data EncodedTrajectory
  (D : ITD.InvolutiveDynamics)
  (A : ITD.AdmissibleControls D) :
  ITD.State D → Set₁ where
  done : ∀ {s} → EncodedTrajectory D A s
  choose : ∀ {s}
    (C : FiniteAdmissibleCode D A s)
    (code : Code C) →
    EncodedTrajectory D A (ITD.step D s (selectedControl C code)) →
    EncodedTrajectory D A s

trajectoryCodeBits : ∀ {D A s} → EncodedTrajectory D A s → Nat
trajectoryCodeBits done = zero
trajectoryCodeBits (choose C code rest) =
  codeBits C code + trajectoryCodeBits rest

record CodingBoundary : Set where
  constructor boundary
  field
    admissibilityProofCarried : Set
    rankUnrankRequired : Set
    branchCountMustBeInstantiated : Set
    logarithmicOptimalityPromoted : Set

canonicalBoundary : CodingBoundary
canonicalBoundary = boundary Set Set Set Set
