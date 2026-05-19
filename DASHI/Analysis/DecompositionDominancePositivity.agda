module DASHI.Analysis.DecompositionDominancePositivity where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_; _∸_; z≤n)
open import Data.Product using (_×_; _,_)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.ActiveWallStructure as AWS
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
import DASHI.Pressure as P
open import DASHI.TrackedPrimes using (SSP)
open import DASHI.Arithmetic.VpDepth using (minNat)

data DecompositionKind : Set where
  arithmetic wall count : DecompositionKind

record DecompositionSurface
  {ℓS ℓP : Level}
  (State : Set ℓS)
  (Part : Set ℓP) :
  Set (lsuc (ℓS ⊔ ℓP)) where
  field
    kind : DecompositionKind
    leftPart : State → Part
    rightPart : State → Part
    combine : Part → Part → Part
    total : State → Part
    decomposes :
      ∀ s → total s ≡ combine (leftPart s) (rightPart s)

DeltaLocalState : Set
DeltaLocalState = SSP × AIE.Int × AIE.Int

deltaLocalDecomposition : DecompositionSurface DeltaLocalState Nat
deltaLocalDecomposition = record
  { kind = arithmetic
  ; leftPart = λ { (p , x , y) → AIE.gammaAt p x y }
  ; rightPart = λ { (p , x , y) → minNat (AIE.alphaAt p x y) (AIE.betaAt p x y) }
  ; combine = _∸_
  ; total = λ { (p , x , y) → AIE.deltaAt p x y }
  ; decomposes = λ { (p , x , y) → AIE.deltaAt-decomposition p x y }
  }

WallState : Set
WallState = AIE.Int × AIE.Int

wallDecomposition : DecompositionSurface WallState Nat
wallDecomposition = record
  { kind = wall
  ; leftPart = λ { (x , y) → AWS.activeWallCount x y }
  ; rightPart = λ { (x , y) → AWS.supportPrimeCount x y }
  ; combine = _+_
  ; total = λ { (x , y) → AWS.activeWallCount x y + AWS.supportPrimeCount x y }
  ; decomposes = λ { (x , y) → refl }
  }

record CountDecomposition : Set where
  constructor countDecomposition
  field
    triadicCoreCount : Nat
    interfaceCount : Nat

  totalCount : Nat
  totalCount = triadicCoreCount + interfaceCount

open CountDecomposition public

candidateCountDecomposition : CountDecomposition
candidateCountDecomposition = countDecomposition 9 6

countDecompositionSurface :
  DecompositionSurface CountDecomposition Nat
countDecompositionSurface = record
  { kind = count
  ; leftPart = triadicCoreCount
  ; rightPart = interfaceCount
  ; combine = _+_
  ; total = totalCount
  ; decomposes = λ _ → refl
  }

record DominanceSurface
  {ℓS ℓW : Level}
  (State : Set ℓS)
  (Weight : Set ℓW) :
  Set (lsuc (ℓS ⊔ ℓW)) where
  field
    _⊑_ : Weight → Weight → Set
    main : State → Weight
    error : State → Weight
    dominates : ∀ s → error s ⊑ main s

activeWallDominance : DominanceSurface WallState Nat
activeWallDominance = record
  { _⊑_ = _≤_
  ; main = λ { (x , y) → AWS.supportPrimeCount x y }
  ; error = λ { (x , y) → AWS.activeWallCount x y }
  ; dominates = λ { (x , y) → AWS.activeWallCount≤supportPrimeCount x y }
  }

record PressureDominanceSurface (State : Set) : Set₁ where
  field
    mainPressure : State → P.Pressure
    errorPressure : State → P.Pressure
    pressureDominates :
      ∀ s → errorPressure s P.⊑p mainPressure s

record PositivitySurface
  {ℓS ℓW ℓP : Level}
  (State : Set ℓS)
  (Weight : Set ℓW)
  (Positive : Weight → Set ℓP) :
  Set (lsuc (ℓS ⊔ ℓW ⊔ ℓP)) where
  field
    measure : State → Weight
    positive : ∀ s → Positive (measure s)
    analyticClosureClaim : Set ℓP
    noAnalyticClosureClaim : ⊤

NatPositive : Nat → Set
NatPositive n = 0 ≤ n

natPositive : ∀ n → NatPositive n
natPositive _ = z≤n

weightedValuationPositivity :
  PositivitySurface AIE.Int Nat NatPositive
weightedValuationPositivity = record
  { measure = WVE.weightedValuationEnergy
  ; positive = λ s → natPositive (WVE.weightedValuationEnergy s)
  ; analyticClosureClaim = ⊤
  ; noAnalyticClosureClaim = tt
  }

weightedQuadraticPositivity :
  PositivitySurface AIE.Int Nat NatPositive
weightedQuadraticPositivity = record
  { measure = WVE.weightedQuadraticEnergy
  ; positive = λ s → natPositive (WVE.weightedQuadraticEnergy s)
  ; analyticClosureClaim = ⊤
  ; noAnalyticClosureClaim = tt
  }

record DecompositionDominancePositivityPack : Set₁ where
  field
    arithmeticDecomposition :
      DecompositionSurface DeltaLocalState Nat
    wallSurface :
      DecompositionSurface WallState Nat
    heckeCountSurface :
      DecompositionSurface CountDecomposition Nat
    wallDominance :
      DominanceSurface WallState Nat
    linearValuationPositivity :
      PositivitySurface AIE.Int Nat NatPositive
    quadraticValuationPositivity :
      PositivitySurface AIE.Int Nat NatPositive

decompositionDominancePositivityPack :
  DecompositionDominancePositivityPack
decompositionDominancePositivityPack = record
  { arithmeticDecomposition = deltaLocalDecomposition
  ; wallSurface = wallDecomposition
  ; heckeCountSurface = countDecompositionSurface
  ; wallDominance = activeWallDominance
  ; linearValuationPositivity = weightedValuationPositivity
  ; quadraticValuationPositivity = weightedQuadraticPositivity
  }
