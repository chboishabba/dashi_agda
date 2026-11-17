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
open import Data.Rational using (ℚ; _*_; Positive)
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
