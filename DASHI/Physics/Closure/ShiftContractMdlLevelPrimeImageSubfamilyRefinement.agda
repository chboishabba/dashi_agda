module DASHI.Physics.Closure.ShiftContractMdlLevelPrimeImageSubfamilyRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max; π-mdl-max-separates-obstruction-pair)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState; shiftContractStateTransportedPrimeEmbedding)

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Two-point explicit subfamily on the current noncanonical carrier.
--
-- This is the strongest honest enlargement currently supported by the
-- in-tree explicit witnesses: the retired coarse counterexample pair gives
-- us a finite family of two explicit states, while the strengthened
-- `mdlLevel × π-max` surface still separates the mixed case.

data MdlLevelPrimeImageSubfamily₂ : Set where
  left : MdlLevelPrimeImageSubfamily₂
  right : MdlLevelPrimeImageSubfamily₂

member : MdlLevelPrimeImageSubfamily₂ → ShiftContractState
member left = coarseCounterexampleLeft
member right = coarseCounterexampleRight

primeImage-equal-on-explicit-two-point-subfamily :
  ∀ {x y : MdlLevelPrimeImageSubfamily₂} →
  π-mdl-max (member x) ≡ π-mdl-max (member y) →
  shiftContractStateTransportedPrimeEmbedding (member x)
    ≡
  shiftContractStateTransportedPrimeEmbedding (member y)
primeImage-equal-on-explicit-two-point-subfamily {left} {left} _ = refl
primeImage-equal-on-explicit-two-point-subfamily {right} {right} _ = refl
primeImage-equal-on-explicit-two-point-subfamily {left} {right} eq =
  ⊥-elim (π-mdl-max-separates-obstruction-pair eq)
primeImage-equal-on-explicit-two-point-subfamily {right} {left} eq =
  ⊥-elim (π-mdl-max-separates-obstruction-pair (sym eq))

twoPoint-family-separates-mixed-members :
  π-mdl-max (member left) ≢ π-mdl-max (member right)
twoPoint-family-separates-mixed-members =
  π-mdl-max-separates-obstruction-pair

record ShiftContractMdlLevelPrimeImageSubfamilyRefinement : Set₁ where
  field
    surface :
      MdlLevelCoarseObservable
    witnessLeft :
      MdlLevelPrimeImageSubfamily₂
    witnessRight :
      MdlLevelPrimeImageSubfamily₂
    leftPrimeImage :
      shiftContractStateTransportedPrimeEmbedding (member left)
        ≡
      shiftContractStateTransportedPrimeEmbedding (member left)
    rightPrimeImage :
      shiftContractStateTransportedPrimeEmbedding (member right)
        ≡
      shiftContractStateTransportedPrimeEmbedding (member right)
    mixedCaseRejected :
      π-mdl-max (member left) ≢ π-mdl-max (member right)

canonicalShiftContractMdlLevelPrimeImageSubfamilyRefinement :
  ShiftContractMdlLevelPrimeImageSubfamilyRefinement
canonicalShiftContractMdlLevelPrimeImageSubfamilyRefinement =
  record
    { surface = π-mdl-max coarseCounterexampleLeft
    ; witnessLeft = left
    ; witnessRight = right
    ; leftPrimeImage = refl
    ; rightPrimeImage = refl
    ; mixedCaseRejected = twoPoint-family-separates-mixed-members
    }
