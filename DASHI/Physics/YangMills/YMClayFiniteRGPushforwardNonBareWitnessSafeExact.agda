{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFiniteRGPushforwardNonBareWitnessSafeExact where

------------------------------------------------------------------------
-- R445 *logical* NON-PROMOTION control, genuine finite coarse projection.
--
-- Equal unit fine weights do NOT guarantee equal unit coarse weights
-- after a non-injective projection: fibre cardinality is part of the
-- pushed-forward measure. Here three original fine points project to
-- two coarse points with fibre sizes 2 and 1, respectively.
--
-- This exact finite counterexample rules out the INVALID general
-- inference "a normalized fine law + a block map implies the bare
-- coarse (uniform beta=0) law." It is NOT a counterexample asserting
-- failure for the specifically chosen SU(N) block map or product Haar.
-- The actual R445 continuous SU(N) density/disintegration hypothesis
-- is still a separate genuine physical analytic proof.
--
-- No imported legacy RealAnalysisAxioms, no local postulate, no axioms.
-- Source-written Golden candidate: Agda kernel has NOT been run.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

data FineState : Set where
  fineA0 fineA1 fineB : FineState

data CoarseState : Set where
  coarseA coarseB : CoarseState

allFine : List FineState
allFine = fineA0 ∷ fineA1 ∷ fineB ∷ []

selectedBlock : FineState → CoarseState
selectedBlock fineA0 = coarseA
selectedBlock fineA1 = coarseA
selectedBlock fineB = coarseB

sameCoarseFibreDistinctFine :
  selectedBlock fineA0 ≡ selectedBlock fineA1
sameCoarseFibreDistinctFine = refl

fineA0DifferentFineA1 : fineA0 ≡ fineA1 → ⊥
fineA0DifferentFineA1 ()

indicator : CoarseState → FineState → Nat
indicator coarseA fineA0 = 1
indicator coarseA fineA1 = 1
indicator coarseA fineB  = 0
indicator coarseB fineA0 = 0
indicator coarseB fineA1 = 0
indicator coarseB fineB  = 1

sumFine : (FineState → Nat) → List FineState → Nat
sumFine f [] = 0
sumFine f (x ∷ xs) = f x + sumFine f xs

-- Every fine point has an equal unit weight, analogous to the
-- finite beta=0 high-temperature reference but NOT a YM Haar claim.
fineUnitWeight : FineState → Nat
fineUnitWeight _ = 1

coarsePushforwardMass : CoarseState → Nat
coarsePushforwardMass y =
  sumFine
    (λ x → indicator y x * fineUnitWeight x)
    allFine

coarsePushforwardMassA : coarsePushforwardMass coarseA ≡ 2
coarsePushforwardMassA = refl

coarsePushforwardMassB : coarsePushforwardMass coarseB ≡ 1
coarsePushforwardMassB = refl

coarseBareUniformWeight : CoarseState → Nat
coarseBareUniformWeight _ = 1

twoNotOne : 2 ≡ 1 → ⊥
twoNotOne ()

fourNotThree : 4 ≡ 3 → ⊥
fourNotThree ()

-- No common normalization constant turns the two **actual**
-- pushforward fibre masses into the proposed bare-uniform weights.
-- Both alleged targets would be definitionally equal to that constant.
noBareUniformUnnormalizedClosure :
  ∀ (constant : Nat) →
  coarsePushforwardMass coarseA
    ≡ constant * coarseBareUniformWeight coarseA →
  coarsePushforwardMass coarseB
    ≡ constant * coarseBareUniformWeight coarseB →
  ⊥
noBareUniformUnnormalizedClosure constant aEq bEq =
  twoNotOne (trans (sym coarsePushforwardMassA)
    (trans aEq
      (trans (sym bEq) coarsePushforwardMassB)))

-- Even after normalization, the cross-multiplied ratio of coarseA
-- probabilities is different: (2/3) != (1/2), as 2*2 != 1*3.
noBareUniformNormalizedClosure :
  coarsePushforwardMass coarseA * 2
    ≡ coarseBareUniformWeight coarseA * 3 →
  ⊥
noBareUniformNormalizedClosure impossible =
  fourNotThree impossible

-- Thus the NEW selected continuous SU(N) R445 blocked pushforward may
-- be called a *coarse distribution* but NOT automatically the original
-- bare Wilson Gibbs law; the actual physical block and effective density
-- must be analysed independently.
