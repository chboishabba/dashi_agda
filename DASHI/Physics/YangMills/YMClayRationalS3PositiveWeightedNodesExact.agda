module DASHI.Physics.YangMills.YMClayRationalS3PositiveWeightedNodesExact where

------------------------------------------------------------------------
-- ORIGINAL SOURCE: concrete root-free rational S3 nodes and positive
-- rational area-density weights. No trig, sqrt, implicit sphere,
-- assumed Haar measure, or assumed positive weights.
--
-- Reuse the EXISTING generic Fejer finite weighted-list owner, the
-- concrete stereographic original rational SU2 node, and the
-- existing positive rational reciprocal theorem. The physical
-- all-degree moment and infinite limit still require an analytic
-- Bishop proof. Non-safe due to imported existing non-safe owners.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; Positive)
import Data.Rational.Tactic.RingSolver as ℚRing
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.YMClaySU2FejerProductFiniteExact as Finite
import DASHI.Physics.YangMills.YMClayRationalS3StereographicConcreteExact as Stereo
import DASHI.Physics.YangMills.YMClayRationalS3StereographicNodeExact as Polynomial
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Original

Parameters : Set
Parameters = Finite.Triple ℚ ℚ ℚ

parameterNode : Parameters → Original.RationalUnitQuaternion
parameterNode t =
  Stereo.rationalS3Node
    (Finite.fst t) (Finite.snd t) (Finite.thd t)

rawAreaWeight : Parameters → ℚ
rawAreaWeight t =
  let
    w = Stereo.stereoInverse
      (Finite.fst t) (Finite.snd t) (Finite.thd t)
  in
  (w * w) * w

-- Global 8-factor in the stereographic area density cancels after
-- normalization. The reciprocal cube is therefore the exact
-- rational positive relative weight.
rawAreaWeightPositive : ∀ t → Positive (rawAreaWeight t)
rawAreaWeightPositive t =
  let
    x = Finite.fst t
    y = Finite.snd t
    z = Finite.thd t
    w = Stereo.stereoInverse x y z
    wPositive = Reciprocal.safeRationalReciprocalPositive
      (Polynomial.denominator x y z)
      (Stereo.denominatorPositive x y z)
  in
  ℚP.pos*pos⇒pos
    (ℚP.pos*pos⇒pos wPositive wPositive)
    wPositive

weightedOriginalNode :
  Parameters → Finite.Weighted ℚ Original.RationalUnitQuaternion
weightedOriginalNode t =
  Finite.weighted (parameterNode t) (rawAreaWeight t)

-- This is an inhabited concrete original SU2 weighted list:
-- EVERY node carries the constructed original norm-one witness,
-- EVERY weight has a strictly-positive proof.
rationalS3WeightedNodes :
  List Parameters →
  List (Finite.Weighted ℚ Original.RationalUnitQuaternion)
rationalS3WeightedNodes = Finite.map weightedOriginalNode

rationalS3AllWeightsPositive :
  ∀ parameters →
  Finite.All
    (λ node → Positive (Finite.weight node))
    (rationalS3WeightedNodes parameters)
rationalS3AllWeightsPositive [] = Finite.allNil
rationalS3AllWeightsPositive (t ∷ ts) =
  Finite.allCons
    (rawAreaWeightPositive t)
    (rationalS3AllWeightsPositive ts)


------------------------------------------------------------------------
-- Full FINITE normalized original quaternion probability list.
-- No independent normalization axiom, no arbitrary scalar division:
-- total positive mass follows from positive rational area weights,
-- and the existing rational reciprocal owner supplies its inverse.
------------------------------------------------------------------------

rawMass : List Parameters → ℚ
rawMass [] = 0ℚ
rawMass (t ∷ ts) = rawAreaWeight t + rawMass ts

rawMassNonnegative : ∀ ts → 0ℚ ≤ rawMass ts
rawMassNonnegative [] = ℚP.≤-refl
rawMassNonnegative (t ∷ ts) =
  subst
    (λ lower → lower ≤ rawMass (t ∷ ts))
    (ℚRing.solve [])
    (ℚP.+-mono-≤
      (ℚP.<⇒≤ (rawAreaWeightPositive t))
      (rawMassNonnegative ts))

rawMassPositive :
  ∀ first rest → Positive (rawMass (first ∷ rest))
rawMassPositive first rest =
  subst
    (λ lower → lower < rawMass (first ∷ rest))
    (ℚRing.solve [])
    (ℚP.+-mono-<-≤
      (rawAreaWeightPositive first)
      (rawMassNonnegative rest))

normalizedScale : ∀ first rest → ℚ
normalizedScale first rest =
  Reciprocal.safeRationalReciprocal (rawMass (first ∷ rest))

normalizedScalePositive :
  ∀ first rest → Positive (normalizedScale first rest)
normalizedScalePositive first rest =
  Reciprocal.safeRationalReciprocalPositive
    (rawMass (first ∷ rest)) (rawMassPositive first rest)

normalizedWeight :
  ∀ first rest → Parameters → ℚ
normalizedWeight first rest t =
  rawAreaWeight t * normalizedScale first rest

normalizedOriginalNodes :
  (first : Parameters) (rest : List Parameters) →
  List (Finite.Weighted ℚ Original.RationalUnitQuaternion)
normalizedOriginalNodes first rest =
  Finite.map
    (λ t → Finite.weighted (parameterNode t)
      (normalizedWeight first rest t))
    (first ∷ rest)

normalizedOriginalNodesPositive :
  ∀ first rest →
  Finite.All (λ node → Positive (Finite.weight node))
    (normalizedOriginalNodes first rest)
normalizedOriginalNodesPositive first rest =
  allPositive first rest (first ∷ rest)
  where
  allPositive :
    ∀ first rest ts →
    Finite.All (λ node → Positive (Finite.weight node))
      (Finite.map
        (λ t → Finite.weighted (parameterNode t)
          (normalizedWeight first rest t)) ts)
  allPositive first rest [] = Finite.allNil
  allPositive first rest (t ∷ ts) =
    Finite.allCons
      (ℚP.pos*pos⇒pos
        (rawAreaWeightPositive t)
        (normalizedScalePositive first rest))
      (allPositive first rest ts)

finiteTotalWeight :
  List (Finite.Weighted ℚ Original.RationalUnitQuaternion) → ℚ
finiteTotalWeight [] = 0ℚ
finiteTotalWeight (node ∷ nodes) =
  Finite.weight node + finiteTotalWeight nodes

scaledMass :
  (first : Parameters) (rest ts : List Parameters) →
  ℚ
scaledMass first rest [] = 0ℚ
scaledMass first rest (t ∷ ts) =
  normalizedWeight first rest t + scaledMass first rest ts

normalizedNodesMassByDefinition :
  ∀ first rest ts →
  finiteTotalWeight
    (Finite.map
      (λ t → Finite.weighted (parameterNode t)
        (normalizedWeight first rest t)) ts)
  ≡ scaledMass first rest ts
normalizedNodesMassByDefinition first rest [] = ℚRing.solve []
normalizedNodesMassByDefinition first rest (t ∷ ts) =
  cong (λ tail → normalizedWeight first rest t + tail)
    (normalizedNodesMassByDefinition first rest ts)

scaledMassFactor :
  ∀ first rest ts →
  scaledMass first rest ts ≡ rawMass ts * normalizedScale first rest
scaledMassFactor first rest [] = ℚRing.solve []
scaledMassFactor first rest (t ∷ ts) =
  trans
    (cong (λ tail → normalizedWeight first rest t + tail)
      (scaledMassFactor first rest ts))
    (regroup (rawAreaWeight t) (rawMass ts)
      (normalizedScale first rest))
  where
  regroup : ∀ a b c → a * c + b * c ≡ (a + b) * c
  regroup = ℚRing.solve-∀

normalizedOriginalNodesMassOne :
  ∀ first rest →
  finiteTotalWeight (normalizedOriginalNodes first rest) ≡ 1ℚ
normalizedOriginalNodesMassOne first rest =
  let
    mass = rawMass (first ∷ rest)
    inverse = normalizedScale first rest
  in
  trans
    (normalizedNodesMassByDefinition first rest (first ∷ rest))
    (trans
      (scaledMassFactor first rest (first ∷ rest))
      (trans
        (ℚP.*-comm mass inverse)
        (Reciprocal.safeRationalReciprocalTimesPositive mass
          (rawMassPositive first rest))))
