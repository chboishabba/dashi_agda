module DASHI.Physics.Closure.ShiftContractBalancedComposedFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])

open import DASHI.Algebra.Trit using (neg; pos; zer)
open import DASHI.Physics.Closure.ShiftContractComposedFamily as SCF
  using (composeState)
open import DASHI.Physics.Closure.ShiftContractFullSupportTrajectory as FS
  using (fullSupport)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadic3CycleInstance as ST3
  using
    ( x0
    ; x1
    ; x2
    ; balancedπ-constant
    ; balancedPrimeDistinct01
    ; balancedPrimeDistinct02
    ; balancedPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2; triadicCycle)

------------------------------------------------------------------------
-- Balanced cyclic branch, rebuilt through the composed-generator lane.
--
-- The previous composed surface recovered the dense width-three branch from a
-- shared base plus varying cut masks. This module upgrades that idea to the
-- first genuinely balanced same-carrier cycle:
-- start from `fullSupport`, choose one tail coordinate to zero out, and a
-- different tail coordinate to overwrite with `neg`. The resulting ternary
-- interaction reproduces the concrete balanced 3-cycle exactly.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

cutMask0 : ShiftContractState
cutMask0 = zer ∷ zer ∷ pos ∷ zer ∷ []

cutMask1 : ShiftContractState
cutMask1 = zer ∷ pos ∷ zer ∷ zer ∷ []

cutMask2 : ShiftContractState
cutMask2 = zer ∷ zer ∷ zer ∷ pos ∷ []

negRestore0 : ShiftContractState
negRestore0 = zer ∷ zer ∷ zer ∷ neg ∷ []

negRestore1 : ShiftContractState
negRestore1 = zer ∷ zer ∷ neg ∷ zer ∷ []

negRestore2 : ShiftContractState
negRestore2 = zer ∷ neg ∷ zer ∷ zer ∷ []

cutMaskAt : TriadicIndex → ShiftContractState
cutMaskAt i0 = cutMask0
cutMaskAt i1 = cutMask1
cutMaskAt i2 = cutMask2

negRestoreAt : TriadicIndex → ShiftContractState
negRestoreAt i0 = negRestore0
negRestoreAt i1 = negRestore1
negRestoreAt i2 = negRestore2

balancedComposedGen : TriadicIndex → ShiftContractState
balancedComposedGen i =
  composeState fullSupport (cutMaskAt i) (negRestoreAt i)

balancedComposed≡x0 : balancedComposedGen i0 ≡ x0
balancedComposed≡x0 = refl

balancedComposed≡x1 : balancedComposedGen i1 ≡ x1
balancedComposed≡x1 = refl

balancedComposed≡x2 : balancedComposedGen i2 ≡ x2
balancedComposed≡x2 = refl

balancedComposed-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (balancedComposedGen i) ≡ π-mdl-max (balancedComposedGen j)
balancedComposed-π-mdl-max-constant i0 i0 = refl
balancedComposed-π-mdl-max-constant i0 i1
  rewrite balancedComposed≡x0 | balancedComposed≡x1 =
  balancedπ-constant i0 i1
balancedComposed-π-mdl-max-constant i0 i2
  rewrite balancedComposed≡x0 | balancedComposed≡x2 =
  balancedπ-constant i0 i2
balancedComposed-π-mdl-max-constant i1 i0
  rewrite balancedComposed≡x1 | balancedComposed≡x0 =
  balancedπ-constant i1 i0
balancedComposed-π-mdl-max-constant i1 i1 = refl
balancedComposed-π-mdl-max-constant i1 i2
  rewrite balancedComposed≡x1 | balancedComposed≡x2 =
  balancedπ-constant i1 i2
balancedComposed-π-mdl-max-constant i2 i0
  rewrite balancedComposed≡x2 | balancedComposed≡x0 =
  balancedπ-constant i2 i0
balancedComposed-π-mdl-max-constant i2 i1
  rewrite balancedComposed≡x2 | balancedComposed≡x1 =
  balancedπ-constant i2 i1
balancedComposed-π-mdl-max-constant i2 i2 = refl

balancedComposedPrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i1)
balancedComposedPrimeDistinct01
  rewrite balancedComposed≡x0 | balancedComposed≡x1 =
  balancedPrimeDistinct01

balancedComposedPrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i2)
balancedComposedPrimeDistinct02
  rewrite balancedComposed≡x0 | balancedComposed≡x2 =
  balancedPrimeDistinct02

balancedComposedPrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i1)
    ≢
  shiftContractStateTransportedPrimeEmbedding (balancedComposedGen i2)
balancedComposedPrimeDistinct12
  rewrite balancedComposed≡x1 | balancedComposed≡x2 =
  balancedPrimeDistinct12

record ShiftContractBalancedComposedFamily : Set₁ where
  field
    base : ShiftContractState
    cutMask : TriadicIndex → ShiftContractState
    negRestore : TriadicIndex → ShiftContractState
    gen : TriadicIndex → ShiftContractState
    sameSurface :
      ∀ i j →
      π-mdl-max (gen i) ≡ π-mdl-max (gen j)
    cycle3 :
      ∀ i →
      STF.triadicNext (STF.triadicNext (STF.triadicNext i)) ≡ i
    primeSplit01 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i1)
    primeSplit02 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)
    primeSplit12 :
      shiftContractStateTransportedPrimeEmbedding (gen i1)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)
    recoversBalancedCycle0 : gen i0 ≡ x0
    recoversBalancedCycle1 : gen i1 ≡ x1
    recoversBalancedCycle2 : gen i2 ≡ x2

canonicalShiftContractBalancedComposedFamily :
  ShiftContractBalancedComposedFamily
canonicalShiftContractBalancedComposedFamily =
  record
    { base = fullSupport
    ; cutMask = cutMaskAt
    ; negRestore = negRestoreAt
    ; gen = balancedComposedGen
    ; sameSurface = balancedComposed-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = balancedComposedPrimeDistinct01
    ; primeSplit02 = balancedComposedPrimeDistinct02
    ; primeSplit12 = balancedComposedPrimeDistinct12
    ; recoversBalancedCycle0 = balancedComposed≡x0
    ; recoversBalancedCycle1 = balancedComposed≡x1
    ; recoversBalancedCycle2 = balancedComposed≡x2
    }

open ShiftContractBalancedComposedFamily public
