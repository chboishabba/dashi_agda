module DASHI.Combinatorics.TextileBraidRewriteGroupoidExact where

open import DASHI.Core.Prelude
open import Data.List using (map; reverse; _++_)
open import Data.List.Properties using (++-assoc; reverse-involutive)

import DASHI.Combinatorics.TextileNFibreCalculusExact as T

------------------------------------------------------------------------
-- n-fibre braid rewrite / path calculus.
--
-- This owner strengthens the recipe-level textile kernel into a process
-- calculus.  Literal words, executable composition, local inverse reduction,
-- distant-generator commutation and Yang--Baxter rewriting remain distinct.
------------------------------------------------------------------------

flipOrientation : T.CrossingOrientation → T.CrossingOrientation
flipOrientation T.overCrossing = T.underCrossing
flipOrientation T.underCrossing = T.overCrossing

flipOrientationInvolutive :
  (o : T.CrossingOrientation) →
  flipOrientation (flipOrientation o) ≡ o
flipOrientationInvolutive T.overCrossing = refl
flipOrientationInvolutive T.underCrossing = refl

inverseCrossing : {n : Nat} → T.AdjacentCrossing n → T.AdjacentCrossing n
inverseCrossing (T.sigma i o p) = T.sigma i (flipOrientation o) p

inverseCrossingInvolutive :
  {n : Nat} →
  (c : T.AdjacentCrossing n) →
  inverseCrossing (inverseCrossing c) ≡ c
inverseCrossingInvolutive (T.sigma i T.overCrossing p) = refl
inverseCrossingInvolutive (T.sigma i T.underCrossing p) = refl

inverseWord : {n : Nat} → T.BraidWord n → T.BraidWord n
inverseWord w = reverse (map inverseCrossing w)

------------------------------------------------------------------------
-- Composition is ordered concatenation.  This is path composition, not a
-- claim that all different words with one endpoint become equal.
------------------------------------------------------------------------

_▷_ : {n : Nat} → T.BraidWord n → T.BraidWord n → T.BraidWord n
u ▷ v = u ++ v

composeAssociative :
  {n : Nat} →
  (u v w : T.BraidWord n) →
  (u ▷ v) ▷ w ≡ u ▷ (v ▷ w)
composeAssociative u v w = ++-assoc u v w

------------------------------------------------------------------------
-- Distant generators may commute when their supports are disjoint.
------------------------------------------------------------------------

FarSeparated : Nat → Nat → Set
FarSeparated i j = (i + 2 ≤ j) ⊎ (j + 2 ≤ i)

data LocalBraidRewrite (n : Nat) : T.BraidWord n → T.BraidWord n → Set where
  cancelWithInverse :
    (c : T.AdjacentCrossing n) →
    LocalBraidRewrite n
      (c ∷ inverseCrossing c ∷ [])
      []

  insertInversePair :
    (c : T.AdjacentCrossing n) →
    LocalBraidRewrite n
      []
      (c ∷ inverseCrossing c ∷ [])

  farCommute :
    (a b : T.AdjacentCrossing n) →
    FarSeparated (T.leftIndex a) (T.leftIndex b) →
    LocalBraidRewrite n
      (a ∷ b ∷ [])
      (b ∷ a ∷ [])

------------------------------------------------------------------------
-- Concrete 4-fibre distant-generator relation sigma_0 sigma_2 =
-- sigma_2 sigma_0 at rewrite level.
------------------------------------------------------------------------

fourHasSigma0 : 0 + 2 ≤ 4
fourHasSigma0 = s≤s (s≤s z≤n)

fourHasSigma2 : 2 + 2 ≤ 4
fourHasSigma2 = ≤-refl

sigma0-4 : T.AdjacentCrossing 4
sigma0-4 = T.sigma 0 T.overCrossing fourHasSigma0

sigma2-4 : T.AdjacentCrossing 4
sigma2-4 = T.sigma 2 T.overCrossing fourHasSigma2

sigma0Sigma2FarSeparated : FarSeparated 0 2
sigma0Sigma2FarSeparated = inj₁ ≤-refl

fourFibreFarCommutation :
  LocalBraidRewrite 4
    (sigma0-4 ∷ sigma2-4 ∷ [])
    (sigma2-4 ∷ sigma0-4 ∷ [])
fourFibreFarCommutation =
  farCommute sigma0-4 sigma2-4 sigma0Sigma2FarSeparated

------------------------------------------------------------------------
-- Context closure: a local rewrite can be applied inside arbitrary prefix and
-- suffix history.  This is what makes the relation useful on long n-fibre
-- recipes rather than only on two-generator toy words.
------------------------------------------------------------------------

data ContextualBraidRewrite (n : Nat) : T.BraidWord n → T.BraidWord n → Set where
  contextualRewrite :
    {u v : T.BraidWord n} →
    (prefix suffix : T.BraidWord n) →
    LocalBraidRewrite n u v →
    ContextualBraidRewrite n
      (prefix ++ u ++ suffix)
      (prefix ++ v ++ suffix)

------------------------------------------------------------------------
-- Reflexive/symmetric/transitive closure gives process equivalence while
-- retaining literal histories as separate data.
------------------------------------------------------------------------

data BraidProcessEquivalent (n : Nat) : T.BraidWord n → T.BraidWord n → Set where
  processRefl :
    {w : T.BraidWord n} →
    BraidProcessEquivalent n w w

  processStep :
    {u v : T.BraidWord n} →
    ContextualBraidRewrite n u v →
    BraidProcessEquivalent n u v

  processSym :
    {u v : T.BraidWord n} →
    BraidProcessEquivalent n u v →
    BraidProcessEquivalent n v u

  processTrans :
    {u v w : T.BraidWord n} →
    BraidProcessEquivalent n u v →
    BraidProcessEquivalent n v w →
    BraidProcessEquivalent n u w

fourFibreFarCommutationEquivalent :
  BraidProcessEquivalent 4
    (sigma0-4 ∷ sigma2-4 ∷ [])
    (sigma2-4 ∷ sigma0-4 ∷ [])
fourFibreFarCommutationEquivalent =
  processStep (contextualRewrite [] [] fourFibreFarCommutation)

------------------------------------------------------------------------
-- Explicit inverse examples.  We keep the generic definition but only claim
-- reductions for concrete words here unless/until the generic list lemmas are
-- wired into a full group proof.
------------------------------------------------------------------------

inverseSigma0-3 :
  inverseCrossing T.sigma0-3
  ≡
  T.sigma 0 T.underCrossing T.threeHasSigma0
inverseSigma0-3 = refl

threeLeftInverseWord : T.BraidWord 3
threeLeftInverseWord = inverseWord T.threeFibreYangBaxterLeft

threeLeftInverseWordExact :
  threeLeftInverseWord
  ≡
  (T.sigma 0 T.underCrossing T.threeHasSigma0
   ∷ T.sigma 1 T.underCrossing T.threeHasSigma1
   ∷ T.sigma 0 T.underCrossing T.threeHasSigma0
   ∷ [])
threeLeftInverseWordExact = refl

------------------------------------------------------------------------
-- Braid paths retain source word, destination word and proof-relevant rewrite
-- history.  The endpoint words alone are therefore not the whole process.
------------------------------------------------------------------------

record BraidRewritePath (n : Nat) : Set where
  constructor braidRewritePath
  field
    sourceWord : T.BraidWord n
    targetWord : T.BraidWord n
    processReceipt : BraidProcessEquivalent n sourceWord targetWord

open BraidRewritePath public

canonicalFourFibreRewritePath : BraidRewritePath 4
canonicalFourFibreRewritePath =
  braidRewritePath
    (sigma0-4 ∷ sigma2-4 ∷ [])
    (sigma2-4 ∷ sigma0-4 ∷ [])
    fourFibreFarCommutationEquivalent

------------------------------------------------------------------------
-- Requested nMin floor remains available at the stronger rewrite level.
------------------------------------------------------------------------

rewriteCalculusNMin : Nat
rewriteCalculusNMin = T.nMinFibreTarget

rewriteCalculusNMinIs15 : rewriteCalculusNMin ≡ 15
rewriteCalculusNMinIs15 = refl

fifteenFibreCanonicalWord : T.BraidWord 15
fifteenFibreCanonicalWord = T.braidSteps T.braid15

fifteenFibreCanonicalWordExact :
  fifteenFibreCanonicalWord ≡ T.allAdjacentCrossings 13
fifteenFibreCanonicalWordExact = T.braid15IsFullAdjacentSweep

------------------------------------------------------------------------
-- Boundary record.
------------------------------------------------------------------------

record BraidRewriteBoundary : Set where
  constructor braidRewriteBoundary
  field
    sameGeneratorMultisetImpliesLiteralWordEquality : Bool
    sameGeneratorMultisetImpliesLiteralWordEqualityIsFalse :
      sameGeneratorMultisetImpliesLiteralWordEquality ≡ false

    processEquivalentImpliesHistoryErased : Bool
    processEquivalentImpliesHistoryErasedIsFalse :
      processEquivalentImpliesHistoryErased ≡ false

    concreteFourFibreRelationProvesAllGenericRelations : Bool
    concreteFourFibreRelationProvesAllGenericRelationsIsFalse :
      concreteFourFibreRelationProvesAllGenericRelations ≡ false

    inverseDefinitionAloneClaimsFullBraidGroup : Bool
    inverseDefinitionAloneClaimsFullBraidGroupIsFalse :
      inverseDefinitionAloneClaimsFullBraidGroup ≡ false

open BraidRewriteBoundary public

canonicalBraidRewriteBoundary : BraidRewriteBoundary
canonicalBraidRewriteBoundary =
  braidRewriteBoundary false refl false refl false refl false refl
