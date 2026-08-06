module DASHI.Physics.Closure.NSTriadKNLuoFiniteThreePairCoefficientExact where

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
-- Derive the physical pair coefficient equality from the proved finite
-- weighted-character theorem.  The source contribution is the literal
-- weighted-increment coefficient times the tensor coefficient; the target is
-- the canonical multiplier times the same tensor coefficient.  Congruence
-- proves equality for each pair, and the existing map/fold theorem proves the
-- whole-fold equality for each of the three Luo pair families.
--
-- Pair selection, shell ownership and reality/conjugation policy remain
-- separate geometric obligations.  The coefficient equality itself is no
-- longer a primitive field on a finite character realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Finite
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterMultiplierBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNLuoIncrementKernelFourierMultiplierExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPointwisePairFoldReductionExact as Pointwise
import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellTermFoldExact as Fold

record FiniteThreePairCarrier
    (system : Finite.FiniteCharacterSystem) : Set₁ where
  field
    Pair : Set

    leftMode rightMode : Pair → Finite.Mode system
    tensorCoefficient : Pair → ℚ

    lowIncrementPairs : List Pair
    highIncrementPairs : List Pair
    highTailPairs : List Pair

open FiniteThreePairCarrier public

spatialPairContribution :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Pair carrier →
  ℚ
spatialPairContribution {system} carrier pair =
  Finite.finiteWeightedIncrement
    system
    (leftMode carrier pair)
    (rightMode carrier pair)
  * tensorCoefficient carrier pair

multiplierPairContribution :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Pair carrier →
  ℚ
multiplierPairContribution {system} carrier pair =
  Multiplier.pairMultiplier
    (Bridge.finitePeriodicIncrementMultiplierData system)
    (leftMode carrier pair)
    (rightMode carrier pair)
  * tensorCoefficient carrier pair

finitePairCoefficientIdentification :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
    (pair : Pair carrier) →
  spatialPairContribution carrier pair
  ≡ multiplierPairContribution carrier pair
finitePairCoefficientIdentification {system} carrier pair =
  cong
    (λ multiplier → multiplier * tensorCoefficient carrier pair)
    (Bridge.finiteWeightedIncrementEqualsPairMultiplier
      system
      (leftMode carrier pair)
      (rightMode carrier pair))

finitePairFamilyIdentification :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
    (pairs : List (Pair carrier)) →
  Pointwise.PointwisePairIdentification
    {Pair = Pair carrier}
    {Contribution = ℚ}
    pairs
finitePairFamilyIdentification carrier pairs = record
  { sourceContribution = spatialPairContribution carrier
  ; targetContribution = multiplierPairContribution carrier
  ; pairwiseIdentification =
      finitePairCoefficientIdentification carrier
  }

lowIncrementPairCoefficientIdentification :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Pointwise.PointwisePairIdentification
    {Pair = Pair carrier}
    {Contribution = ℚ}
    (lowIncrementPairs carrier)
lowIncrementPairCoefficientIdentification carrier =
  finitePairFamilyIdentification carrier (lowIncrementPairs carrier)

highIncrementPairCoefficientIdentification :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Pointwise.PointwisePairIdentification
    {Pair = Pair carrier}
    {Contribution = ℚ}
    (highIncrementPairs carrier)
highIncrementPairCoefficientIdentification carrier =
  finitePairFamilyIdentification carrier (highIncrementPairs carrier)

highTailPairCoefficientIdentification :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Pointwise.PointwisePairIdentification
    {Pair = Pair carrier}
    {Contribution = ℚ}
    (highTailPairs carrier)
highTailPairCoefficientIdentification carrier =
  finitePairFamilyIdentification carrier (highTailPairs carrier)

finitePairWholeFoldIdentity :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
    (pairs : List (Pair carrier)) →
  Fold.foldList _+_ 0ℚ
    (Fold.mapList (spatialPairContribution carrier) pairs)
  ≡
  Fold.foldList _+_ 0ℚ
    (Fold.mapList (multiplierPairContribution carrier) pairs)
finitePairWholeFoldIdentity carrier pairs =
  Pointwise.pointwiseIdentificationGivesFoldIdentification
    (finitePairFamilyIdentification carrier pairs)
    _+_
    0ℚ

lowIncrementWholeFoldIdentity :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (spatialPairContribution carrier)
      (lowIncrementPairs carrier))
  ≡
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (multiplierPairContribution carrier)
      (lowIncrementPairs carrier))
lowIncrementWholeFoldIdentity carrier =
  finitePairWholeFoldIdentity carrier (lowIncrementPairs carrier)

highIncrementWholeFoldIdentity :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (spatialPairContribution carrier)
      (highIncrementPairs carrier))
  ≡
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (multiplierPairContribution carrier)
      (highIncrementPairs carrier))
highIncrementWholeFoldIdentity carrier =
  finitePairWholeFoldIdentity carrier (highIncrementPairs carrier)

highTailWholeFoldIdentity :
  ∀ {system}
    (carrier : FiniteThreePairCarrier system) →
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (spatialPairContribution carrier)
      (highTailPairs carrier))
  ≡
  Fold.foldList _+_ 0ℚ
    (Fold.mapList
      (multiplierPairContribution carrier)
      (highTailPairs carrier))
highTailWholeFoldIdentity carrier =
  finitePairWholeFoldIdentity carrier (highTailPairs carrier)

finiteThreePairCoefficientIdentitiesClosed : Bool
finiteThreePairCoefficientIdentitiesClosed = true

finiteThreePairWholeFoldIdentitiesClosed : Bool
finiteThreePairWholeFoldIdentitiesClosed = true

finiteThreePairCoefficientIdentitiesClosedIsTrue :
  finiteThreePairCoefficientIdentitiesClosed ≡ true
finiteThreePairCoefficientIdentitiesClosedIsTrue = refl

finiteThreePairWholeFoldIdentitiesClosedIsTrue :
  finiteThreePairWholeFoldIdentitiesClosed ≡ true
finiteThreePairWholeFoldIdentitiesClosedIsTrue = refl
