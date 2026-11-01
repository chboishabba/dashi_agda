module DASHI.Biology.SelfIndexingHyperfabricTetrationExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Strong self-indexing tower.  The whole level-n carrier becomes the index
-- set for a nine-valued field at level n+1:
--
--   I_0 = unit,
--   I_(n+1) = I_n -> Fin 9.
--
-- The corresponding cardinality recursion is genuine fixed-base tetration,
-- not ordinary product/tensor growth.

SelfIndexedCarrier : Nat → Set
SelfIndexedCarrier zero = ⊤
SelfIndexedCarrier (suc n) = SelfIndexedCarrier n → Fin 9

selfIndexedSiteCount : Nat → Nat
selfIndexedSiteCount zero = 1
selfIndexedSiteCount (suc n) =
  Hyper.powNat 9 (selfIndexedSiteCount n)

selfIndexedCountEqualsNineTetration :
  (n : Nat) → selfIndexedSiteCount n ≡ Hyper.nineTetration n
selfIndexedCountEqualsNineTetration zero = refl
selfIndexedCountEqualsNineTetration (suc n)
  rewrite selfIndexedCountEqualsNineTetration n = refl

selfIndexedLevelOneHasNineSites : selfIndexedSiteCount 1 ≡ 9
selfIndexedLevelOneHasNineSites = refl

selfIndexedLevelTwoHasNineToNineSites :
  selfIndexedSiteCount 2 ≡ Hyper.powNat 9 9
selfIndexedLevelTwoHasNineToNineSites = refl

------------------------------------------------------------------------
-- 3/6/9 decomposition and transport metadata for each hyperfibre.

data FabricResolution : Set where
  resolution3 : FabricResolution
  resolution6 : FabricResolution
  resolution9 : FabricResolution

resolutionWidth : FabricResolution → Nat
resolutionWidth resolution3 = 3
resolutionWidth resolution6 = 6
resolutionWidth resolution9 = 9

record Hyperfibre {Base : Set} (State : Base → Set) : Set₁ where
  constructor hyperfibre
  field
    Residual : Base → Set
    Path : Base → Base → Set
    transport :
      {source target : Base} →
      Path source target → State source → State target
    residualAt :
      {source target : Base} →
      Path source target → State source → Residual target
    resolutionAt : Base → FabricResolution

------------------------------------------------------------------------
-- Typed description length is kept separate from the length of the generated
-- weave.  This is the finite checked precursor to a machine-relative MDL or
-- Kolmogorov-complexity comparison.

record WeaveComplexity : Set where
  constructor weaveComplexity
  field
    programLength : Nat
    executionLength : Nat
    normalFormLength : Nat
    typeWitnessLength : Nat
    residualWitnessLength : Nat

open WeaveComplexity public

typedDescriptionLength : WeaveComplexity → Nat
typedDescriptionLength complexity =
  programLength complexity
  + normalFormLength complexity
  + typeWitnessLength complexity
  + residualWitnessLength complexity

canonicalSelfIndexingWeaveComplexity : WeaveComplexity
canonicalSelfIndexingWeaveComplexity =
  weaveComplexity 2 9 2 1 1

canonicalTypedDescriptionLengthIsSix :
  typedDescriptionLength canonicalSelfIndexingWeaveComplexity ≡ 6
canonicalTypedDescriptionLengthIsSix = refl

canonicalExecutionLengthIsNine :
  executionLength canonicalSelfIndexingWeaveComplexity ≡ 9
canonicalExecutionLengthIsNine = refl

record SelfIndexingHyperfabricBoundary : Set where
  constructor selfIndexingHyperfabricBoundary
  field
    productTowerAndSelfIndexingTowerAreDefinitionallySame : Bool
    productTowerAndSelfIndexingTowerAreDefinitionallySameIsFalse :
      productTowerAndSelfIndexingTowerAreDefinitionallySame ≡ false

    finiteTypedDescriptionIsMachineIndependentKolmogorovComplexity : Bool
    finiteTypedDescriptionIsMachineIndependentKolmogorovComplexityIsFalse :
      finiteTypedDescriptionIsMachineIndependentKolmogorovComplexity ≡ false

    selfIndexingCarrierAutomaticallySuppliesPhysicalDynamics : Bool
    selfIndexingCarrierAutomaticallySuppliesPhysicalDynamicsIsFalse :
      selfIndexingCarrierAutomaticallySuppliesPhysicalDynamics ≡ false

open SelfIndexingHyperfabricBoundary public

canonicalSelfIndexingHyperfabricBoundary : SelfIndexingHyperfabricBoundary
canonicalSelfIndexingHyperfabricBoundary =
  selfIndexingHyperfabricBoundary false refl false refl false refl
