module DASHI.Cognition.RecursiveFibreTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PhaseEnrichedTrit as Phase

------------------------------------------------------------------------
-- Two recursions must be distinguished.
--
-- 1. Recursive fibre formation adds hidden phase coordinates while preserving
--    a lower observable.
-- 2. A literal exponent tower arises from iterated ternary-valued function
--    spaces Level(n+1) = Level(n) -> TriTruth.
--
-- When Level(n) is finite with a(n) elements, the next function space has
-- 3 ^ a(n) elements.  The code below proves the recurrence numerically and
-- constructs explicit lossless codes for the first two levels.  The distinct
-- transformer recurrence X(n+1)=X(n)->X(n) would instead have size
-- a(n+1)=a(n)^a(n) and is not silently identified with ordinary tetration.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

tetration : Nat → Nat → Nat
tetration base zero = 1
tetration base (suc height) = pow base (tetration base height)

tetrationStep : (base height : Nat) →
  tetration base (suc height) ≡ pow base (tetration base height)
tetrationStep base height = refl

triadicTetrationZero : tetration 3 0 ≡ 1
triadicTetrationZero = refl

triadicTetrationOne : tetration 3 1 ≡ 3
triadicTetrationOne = refl

triadicTetrationTwo : tetration 3 2 ≡ 27
triadicTetrationTwo = refl

triadicTetrationThree : tetration 3 3 ≡ pow 3 27
triadicTetrationThree = refl

------------------------------------------------------------------------
-- Literal function-space hierarchy.
------------------------------------------------------------------------

PredicateLevel : Nat → Set
PredicateLevel zero = ⊤
PredicateLevel (suc level) = PredicateLevel level → Base.TriTruth

predicateLevelSizeRecurrence : Nat → Nat
predicateLevelSizeRecurrence level = tetration 3 level

levelZeroPoint : PredicateLevel zero
levelZeroPoint = tt

levelOneLow : PredicateLevel 1
levelOneLow _ = Base.tri-low

levelOneMid : PredicateLevel 1
levelOneMid _ = Base.tri-mid

levelOneHigh : PredicateLevel 1
levelOneHigh _ = Base.tri-high

-- Level one is losslessly represented by one ternary coordinate.

encodeLevelOne : PredicateLevel 1 → Base.TriTruth
encodeLevelOne function = function tt

decodeLevelOne : Base.TriTruth → PredicateLevel 1
decodeLevelOne value _ = value

levelOneDecodeEncodePointwise :
  (function : PredicateLevel 1) → (unit : ⊤) →
  decodeLevelOne (encodeLevelOne function) unit ≡ function unit
levelOneDecodeEncodePointwise function tt with function tt
... | Base.tri-low = refl
... | Base.tri-mid = refl
... | Base.tri-high = refl

levelOneEncodeDecode :
  (value : Base.TriTruth) →
  encodeLevelOne (decodeLevelOne value) ≡ value
levelOneEncodeDecode Base.tri-low = refl
levelOneEncodeDecode Base.tri-mid = refl
levelOneEncodeDecode Base.tri-high = refl

-- Level two is a ternary-valued function on the three level-one functions and
-- is losslessly represented by three ternary coordinates: 3^3 = 27 codes.

LevelTwoCode : Set
LevelTwoCode =
  Base.TriTruth × (Base.TriTruth × Base.TriTruth)

encodeLevelTwo : PredicateLevel 2 → LevelTwoCode
encodeLevelTwo function =
  function levelOneLow ,
  (function levelOneMid , function levelOneHigh)

decodeLevelTwo : LevelTwoCode → PredicateLevel 2
decodeLevelTwo (lowValue , (midValue , highValue)) levelOne with levelOne tt
... | Base.tri-low = lowValue
... | Base.tri-mid = midValue
... | Base.tri-high = highValue

levelTwoDecodeEncodePointwise :
  (function : PredicateLevel 2) →
  (levelOne : PredicateLevel 1) →
  decodeLevelTwo (encodeLevelTwo function) levelOne ≡ function levelOne
levelTwoDecodeEncodePointwise function levelOne with levelOne tt
... | Base.tri-low = refl
... | Base.tri-mid = refl
... | Base.tri-high = refl

levelTwoEncodeDecode :
  (code : LevelTwoCode) →
  encodeLevelTwo (decodeLevelTwo code) ≡ code
levelTwoEncodeDecode (lowValue , (midValue , highValue)) = refl

levelTwoCodeCount : Nat
levelTwoCodeCount = tetration 3 2

levelTwoCodeCountIsTwentySeven : levelTwoCodeCount ≡ 27
levelTwoCodeCountIsTwentySeven = refl

------------------------------------------------------------------------
-- Recursive phase fibres.  Each refinement stores another hidden phase while
-- the observation recursively forgets those phases and returns the base trit.
------------------------------------------------------------------------

data RecursivePhaseFibre : Nat → Set where
  baseState : BT.Trit → RecursivePhaseFibre zero
  refineState : ∀ {level} →
    RecursivePhaseFibre level →
    Phase.Phase3 →
    RecursivePhaseFibre (suc level)

projectOneLevel : ∀ {level} →
  RecursivePhaseFibre (suc level) → RecursivePhaseFibre level
projectOneLevel (refineState lower phase) = lower

observeBase : ∀ {level} → RecursivePhaseFibre level → BT.Trit
observeBase (baseState value) = value
observeBase (refineState lower phase) = observeBase lower

zeroPoint : (level : Nat) → RecursivePhaseFibre level
zeroPoint zero = baseState BT.zero
zeroPoint (suc level) = refineState (zeroPoint level) Phase.phase0

zeroPointProjects : (level : Nat) →
  projectOneLevel (zeroPoint (suc level)) ≡ zeroPoint level
zeroPointProjects level = refl

zeroPointRemainsObservableZero : (level : Nat) →
  observeBase (zeroPoint level) ≡ BT.zero
zeroPointRemainsObservableZero zero = refl
zeroPointRemainsObservableZero (suc level) =
  zeroPointRemainsObservableZero level

phaseVariant : (level : Nat) → Phase.Phase3 → RecursivePhaseFibre (suc level)
phaseVariant level phase = refineState (zeroPoint level) phase

allPhaseVariantsRemainZero :
  (level : Nat) → (phase : Phase.Phase3) →
  observeBase (phaseVariant level phase) ≡ BT.zero
allPhaseVariantsRemainZero level phase =
  zeroPointRemainsObservableZero level

------------------------------------------------------------------------
-- Generic inverse-system interface.  A coherent family is the formal object
-- behind the claim that a state may be a compatible set of representatives at
-- every refinement level rather than one terminal trit.
------------------------------------------------------------------------

record FibreTower : Set₁ where
  field
    Level   : Nat → Set
    project : (level : Nat) → Level (suc level) → Level level

open FibreTower public

record InverseLimitPoint (tower : FibreTower) : Set where
  field
    stateAt : (level : Nat) → Level tower level
    coherent : (level : Nat) →
      project tower level (stateAt (suc level)) ≡ stateAt level

open InverseLimitPoint public

recursivePhaseTower : FibreTower
recursivePhaseTower = record
  { Level = RecursivePhaseFibre
  ; project = λ level → projectOneLevel
  }

canonicalZeroInverseLimit : InverseLimitPoint recursivePhaseTower
canonicalZeroInverseLimit = record
  { stateAt = zeroPoint
  ; coherent = zeroPointProjects
  }
