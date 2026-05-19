module DASHI.Physics.Closure.ShiftContractComposedFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])

open import DASHI.Algebra.Trit using (Trit; neg; pos; zer)
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using
    ( dense0
    ; dense1
    ; dense2
    ; dense-π-mdl-max-constant
    ; densePrimeDistinct01
    ; densePrimeDistinct02
    ; densePrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractFullSupportTrajectory as FS
  using (fullSupport)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractStateFamily as SCSF
  using
    ( Cyclic3ShiftContractStateFamily
    ; canonicalDenseCyclic3Family
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2; triadicCycle)

------------------------------------------------------------------------
-- First concrete composed generator family on ShiftContractState.
--
-- Rather than hand-writing another explicit family directly, build it from:
-- - a shared base state,
-- - a varying cut mask,
-- - a shared restore mask.
--
-- On the current live carrier, this ternary interaction recovers the dense
-- width-three cyclic family exactly:
--   compose(fullSupport, tailCut, headRestore)
-- which makes the generator class real without inventing abstract algebra the
-- repo does not already carry.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

composeTrit : Trit → Trit → Trit → Trit
composeTrit _ _ pos = pos
composeTrit _ _ neg = neg
composeTrit base pos zer = zer
composeTrit base zer zer = base
composeTrit base neg zer = base

composeState :
  ShiftContractState →
  ShiftContractState →
  ShiftContractState →
  ShiftContractState
composeState
  (a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])
  (b0 ∷ b1 ∷ b2 ∷ b3 ∷ [])
  (c0 ∷ c1 ∷ c2 ∷ c3 ∷ [])
  =
  composeTrit a0 b0 c0
    ∷ composeTrit a1 b1 c1
    ∷ composeTrit a2 b2 c2
    ∷ composeTrit a3 b3 c3
    ∷ []

headRestore : ShiftContractState
headRestore = pos ∷ zer ∷ zer ∷ zer ∷ []

tailCut1 : ShiftContractState
tailCut1 = zer ∷ pos ∷ zer ∷ zer ∷ []

tailCut2 : ShiftContractState
tailCut2 = zer ∷ zer ∷ pos ∷ zer ∷ []

tailCut3 : ShiftContractState
tailCut3 = zer ∷ zer ∷ zer ∷ pos ∷ []

cutMaskAt : TriadicIndex → ShiftContractState
cutMaskAt i0 = tailCut3
cutMaskAt i1 = tailCut2
cutMaskAt i2 = tailCut1

composedGen : TriadicIndex → ShiftContractState
composedGen i = composeState fullSupport (cutMaskAt i) headRestore

composed≡dense0 : composedGen i0 ≡ dense0
composed≡dense0 = refl

composed≡dense1 : composedGen i1 ≡ dense1
composed≡dense1 = refl

composed≡dense2 : composedGen i2 ≡ dense2
composed≡dense2 = refl

composed-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (composedGen i) ≡ π-mdl-max (composedGen j)
composed-π-mdl-max-constant i0 i0 = refl
composed-π-mdl-max-constant i0 i1 rewrite composed≡dense0 | composed≡dense1 =
  dense-π-mdl-max-constant i0 i1
composed-π-mdl-max-constant i0 i2 rewrite composed≡dense0 | composed≡dense2 =
  dense-π-mdl-max-constant i0 i2
composed-π-mdl-max-constant i1 i0 rewrite composed≡dense1 | composed≡dense0 =
  dense-π-mdl-max-constant i1 i0
composed-π-mdl-max-constant i1 i1 = refl
composed-π-mdl-max-constant i1 i2 rewrite composed≡dense1 | composed≡dense2 =
  dense-π-mdl-max-constant i1 i2
composed-π-mdl-max-constant i2 i0 rewrite composed≡dense2 | composed≡dense0 =
  dense-π-mdl-max-constant i2 i0
composed-π-mdl-max-constant i2 i1 rewrite composed≡dense2 | composed≡dense1 =
  dense-π-mdl-max-constant i2 i1
composed-π-mdl-max-constant i2 i2 = refl

composedPrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding (composedGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (composedGen i1)
composedPrimeDistinct01 rewrite composed≡dense0 | composed≡dense1 =
  densePrimeDistinct01

composedPrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding (composedGen i0)
    ≢
  shiftContractStateTransportedPrimeEmbedding (composedGen i2)
composedPrimeDistinct02 rewrite composed≡dense0 | composed≡dense2 =
  densePrimeDistinct02

composedPrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding (composedGen i1)
    ≢
  shiftContractStateTransportedPrimeEmbedding (composedGen i2)
composedPrimeDistinct12 rewrite composed≡dense1 | composed≡dense2 =
  densePrimeDistinct12

record ShiftContractComposedTriadicFamily : Set₁ where
  field
    base : ShiftContractState
    restoreMask : ShiftContractState
    cutMask : TriadicIndex → ShiftContractState
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
    recoversDenseBranch :
      Cyclic3ShiftContractStateFamily.gen canonicalDenseCyclic3Family i0 ≡ gen i0

canonicalShiftContractComposedTriadicFamily :
  ShiftContractComposedTriadicFamily
canonicalShiftContractComposedTriadicFamily =
  record
    { base = fullSupport
    ; restoreMask = headRestore
    ; cutMask = cutMaskAt
    ; gen = composedGen
    ; sameSurface = composed-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = composedPrimeDistinct01
    ; primeSplit02 = composedPrimeDistinct02
    ; primeSplit12 = composedPrimeDistinct12
    ; recoversDenseBranch = refl
    }

open ShiftContractComposedTriadicFamily public
