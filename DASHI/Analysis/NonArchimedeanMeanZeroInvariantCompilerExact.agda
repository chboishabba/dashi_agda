module DASHI.Analysis.NonArchimedeanMeanZeroInvariantCompilerExact where

------------------------------------------------------------------------
-- ZERO-FIBRE INVARIANCE COMPILER
--
-- If an observable `mass` is preserved by one step, then its zero fibre is
-- invariant.  This is the only generic logic needed to turn a column-sum / mass
-- preservation receipt for P_n into invariance of the source's L2_0 kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

record PreservedObservable : Set₁ where
  field
    State Value : Set
    zero : Value
    mass : State → Value
    step : State → State
    preserved : (state : State) → mass (step state) ≡ mass state

open PreservedObservable public

ZeroFibre : (data : PreservedObservable) → State data → Set
ZeroFibre data state = mass data state ≡ zero data

zeroFibreInvariant :
  (data : PreservedObservable) →
  (state : State data) →
  ZeroFibre data state →
  ZeroFibre data (step data state)
zeroFibreInvariant data state hZero =
  trans (preserved data state) hZero

record CollatzMeanZeroSourceBoundary : Set where
  constructor collatzMeanZeroSourceBoundary
  field
    sourceL2ZeroDefinedAsKernelOfSum : Bool
    sourcePnIsHalfDn : Bool
    sourceColumnSumTwoTheoremLocated : Bool
    sourceMassPreservationTheoremLocated : Bool
    genericKernelPreservationNowOwned : Bool

canonicalCollatzMeanZeroSourceBoundary : CollatzMeanZeroSourceBoundary
canonicalCollatzMeanZeroSourceBoundary =
  collatzMeanZeroSourceBoundary true true false false true
