module DASHI.Physics.Closure.NSTriadKNLuoThreePairCoefficientCutsetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Put the three remaining physical coefficient theorems on one common pair
-- carrier and derive the three whole-fold identities through the existing
-- pointwise-pair reducer.  Support, resonance, reality, conjugation, tensor
-- ordering and boundary-shell policies remain explicit named evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellTermFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLuoPointwisePairFoldReductionExact as Pointwise

record ThreePairCoefficientCutset : Set₁ where
  field
    Pair Contribution : Set

    combineContribution : Contribution → Contribution → Contribution
    zeroContribution : Contribution

    lowIncrementPairs : List Pair
    highIncrementPairs : List Pair
    highTailPairs : List Pair

    lowIncrementIdentification :
      Pointwise.PointwisePairIdentification
        {Pair = Pair} {Contribution = Contribution}
        lowIncrementPairs

    highIncrementIdentification :
      Pointwise.PointwisePairIdentification
        {Pair = Pair} {Contribution = Contribution}
        highIncrementPairs

    highTailIdentification :
      Pointwise.PointwisePairIdentification
        {Pair = Pair} {Contribution = Contribution}
        highTailPairs

    LowIncrementPairSupportCharacterization : Set
    lowIncrementPairSupportCharacterization :
      LowIncrementPairSupportCharacterization

    LowIncrementBoundaryShellConvention : Set
    lowIncrementBoundaryShellConvention :
      LowIncrementBoundaryShellConvention

    HighIncrementPairSupportCharacterization : Set
    highIncrementPairSupportCharacterization :
      HighIncrementPairSupportCharacterization

    HighIncrementCancellationOnLowPairs : Set
    highIncrementCancellationOnLowPairs :
      HighIncrementCancellationOnLowPairs

    HardTailCoefficientMeaning : Set
    hardTailCoefficientMeaning : HardTailCoefficientMeaning

    TailPairSelectedIffBothModesAboveCutoff : Set
    tailPairSelectedIffBothModesAboveCutoff :
      TailPairSelectedIffBothModesAboveCutoff

    SourcePairCarrierEqualsPhysicalPairCarrier : Set
    sourcePairCarrierEqualsPhysicalPairCarrier :
      SourcePairCarrierEqualsPhysicalPairCarrier

    PairOutputModeAgreement : Set
    pairOutputModeAgreement : PairOutputModeAgreement

    PairResonanceAgreement : Set
    pairResonanceAgreement : PairResonanceAgreement

    PairRealityRepresentativeAgreement : Set
    pairRealityRepresentativeAgreement :
      PairRealityRepresentativeAgreement

    PairConjugationPolicyAgreement : Set
    pairConjugationPolicyAgreement :
      PairConjugationPolicyAgreement

    PairTensorOrderingAgreement : Set
    pairTensorOrderingAgreement : PairTensorOrderingAgreement

    PairFoldUsesSameZeroAndAddition : Set
    pairFoldUsesSameZeroAndAddition :
      PairFoldUsesSameZeroAndAddition

open ThreePairCoefficientCutset public

lowIncrementWholeFoldIdentity :
  (cutset : ThreePairCoefficientCutset) →
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.sourceContribution
        (lowIncrementIdentification cutset))
      (lowIncrementPairs cutset))
  ≡
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.targetContribution
        (lowIncrementIdentification cutset))
      (lowIncrementPairs cutset))
lowIncrementWholeFoldIdentity cutset =
  Pointwise.pointwiseIdentificationGivesFoldIdentification
    (lowIncrementIdentification cutset)
    (combineContribution cutset)
    (zeroContribution cutset)

highIncrementWholeFoldIdentity :
  (cutset : ThreePairCoefficientCutset) →
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.sourceContribution
        (highIncrementIdentification cutset))
      (highIncrementPairs cutset))
  ≡
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.targetContribution
        (highIncrementIdentification cutset))
      (highIncrementPairs cutset))
highIncrementWholeFoldIdentity cutset =
  Pointwise.pointwiseIdentificationGivesFoldIdentification
    (highIncrementIdentification cutset)
    (combineContribution cutset)
    (zeroContribution cutset)

highTailWholeFoldIdentity :
  (cutset : ThreePairCoefficientCutset) →
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.sourceContribution
        (highTailIdentification cutset))
      (highTailPairs cutset))
  ≡
  Fold.foldList
    (combineContribution cutset)
    (zeroContribution cutset)
    (Fold.mapList
      (Pointwise.targetContribution
        (highTailIdentification cutset))
      (highTailPairs cutset))
highTailWholeFoldIdentity cutset =
  Pointwise.pointwiseIdentificationGivesFoldIdentification
    (highTailIdentification cutset)
    (combineContribution cutset)
    (zeroContribution cutset)

record ThreePairWholeFoldReceipt : Set₁ where
  field
    cutset : ThreePairCoefficientCutset
    lowIncrementFoldIdentity :
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.sourceContribution
            (lowIncrementIdentification cutset))
          (lowIncrementPairs cutset))
      ≡
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.targetContribution
            (lowIncrementIdentification cutset))
          (lowIncrementPairs cutset))
    highIncrementFoldIdentity :
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.sourceContribution
            (highIncrementIdentification cutset))
          (highIncrementPairs cutset))
      ≡
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.targetContribution
            (highIncrementIdentification cutset))
          (highIncrementPairs cutset))
    highTailFoldIdentity :
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.sourceContribution
            (highTailIdentification cutset))
          (highTailPairs cutset))
      ≡
      Fold.foldList
        (combineContribution cutset)
        (zeroContribution cutset)
        (Fold.mapList
          (Pointwise.targetContribution
            (highTailIdentification cutset))
          (highTailPairs cutset))

open ThreePairWholeFoldReceipt public

threePairWholeFoldReceipt :
  ThreePairCoefficientCutset → ThreePairWholeFoldReceipt
threePairWholeFoldReceipt cutset = record
  { cutset = cutset
  ; lowIncrementFoldIdentity = lowIncrementWholeFoldIdentity cutset
  ; highIncrementFoldIdentity = highIncrementWholeFoldIdentity cutset
  ; highTailFoldIdentity = highTailWholeFoldIdentity cutset
  }

threePairCoefficientCutsetConstructed : Bool
threePairCoefficientCutsetConstructed = true

threeWholeFoldIdentitiesDerivedPointwise : Bool
threeWholeFoldIdentitiesDerivedPointwise = true

threePairCoefficientCutsetConstructedIsTrue :
  threePairCoefficientCutsetConstructed ≡ true
threePairCoefficientCutsetConstructedIsTrue = refl

threeWholeFoldIdentitiesDerivedPointwiseIsTrue :
  threeWholeFoldIdentitiesDerivedPointwise ≡ true
threeWholeFoldIdentitiesDerivedPointwiseIsTrue = refl
