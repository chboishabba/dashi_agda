module DASHI.Biology.DNACrossRankInteraction where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (List; []; _∷_)

record RankDetail (A : Set) : Set where
  constructor detail
  field
    rank : Nat
    coefficients : List A
open RankDetail public

record InteractionKernel (A Energy : Set) : Set₁ where
  constructor kernel
  field
    interact : RankDetail A → RankDetail A → Energy
open InteractionKernel public

data CompositionOperation : Set where
  orderedStacking : CompositionOperation
  localConvolution : CompositionOperation
  reverseComplementCorrelation : CompositionOperation
  tensorContraction : CompositionOperation
  quotientAggregation : CompositionOperation
  nonlinearGatedComposition : CompositionOperation

record TypedInteraction (A Energy : Set) : Set₁ where
  constructor typedInteraction
  field
    operation : CompositionOperation
    kernelValue : InteractionKernel A Energy
    sourceRank : Nat
    targetRank : Nat
open TypedInteraction public

record AdditiveEnergy (Energy : Set) : Set₁ where
  constructor additive
  field
    zeroE : Energy
    _⊕_ : Energy → Energy → Energy
open AdditiveEnergy public

foldInteractions :
  ∀ {A Energy : Set} →
  AdditiveEnergy Energy →
  InteractionKernel A Energy →
  List (RankDetail A) →
  List (RankDetail A) →
  Energy
foldInteractions additiveEnergy k [] ys = zeroE additiveEnergy
foldInteractions additiveEnergy k (x ∷ xs) ys =
  foldAgainst x ys ⊕ foldInteractions additiveEnergy k xs ys
  where
  open AdditiveEnergy additiveEnergy
  foldAgainst : RankDetail A → List (RankDetail A) → Energy
  foldAgainst x [] = zeroE
  foldAgainst x (y ∷ rest) = interact k x y ⊕ foldAgainst x rest

natAdditiveEnergy : AdditiveEnergy Nat
natAdditiveEnergy = additive 0 _+_

record DNACrossRankSemantics : Set where
  constructor semantics
  field
    localStackingOperation : CompositionOperation
    hairpinOperation : CompositionOperation
    dimerOperation : CompositionOperation
    gcDebtOperation : CompositionOperation
    operationsAreNotDefinitionallyIdentified : CompositionOperation
open DNACrossRankSemantics public

canonicalDNACrossRankSemantics : DNACrossRankSemantics
canonicalDNACrossRankSemantics =
  semantics
    localConvolution
    reverseComplementCorrelation
    reverseComplementCorrelation
    nonlinearGatedComposition
    orderedStacking
