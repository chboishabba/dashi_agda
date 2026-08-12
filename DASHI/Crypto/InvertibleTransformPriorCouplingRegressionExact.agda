module DASHI.Crypto.InvertibleTransformPriorCouplingRegressionExact where

------------------------------------------------------------------------
-- INVERTIBLE MIXING CAN CREATE TARGET-COORDINATE COUPLING
--
-- Finite exact regression for the NTT prior question. The source carrier is
-- two independent bits. An invertible four-state representation change mixes
-- them into two local target coordinates whose marginal supports are larger
-- than the joint image. Thus local target admissibility does not imply joint
-- admissibility even though the global transform is bijective.
--
-- This is a structural regression, not the FIPS-203 NTT itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record SourcePair : Set where
  constructor sourcePair
  field x y : Bool
open SourcePair public

data U : Set where u0 u1 u2 : U
data V : Set where v0 v1 v4 : V

-- Exactly the four reachable transformed states.
data TargetState : Set where
  t00 t14 t11 t20 : TargetState

uCoord : TargetState → U
uCoord t00 = u0
uCoord t14 = u1
uCoord t11 = u1
uCoord t20 = u2

vCoord : TargetState → V
vCoord t00 = v0
vCoord t14 = v4
vCoord t11 = v1
vCoord t20 = v0

-- Images of the four bit pairs under the Z/5-shaped mixing pattern
-- (x,y) |-> (x+y,x-y):
-- 00 -> (0,0), 01 -> (1,4), 10 -> (1,1), 11 -> (2,0).

encode : SourcePair → TargetState
encode (sourcePair false false) = t00
encode (sourcePair false true)  = t14
encode (sourcePair true false)  = t11
encode (sourcePair true true)   = t20

decode : TargetState → SourcePair
decode t00 = sourcePair false false
decode t14 = sourcePair false true
decode t11 = sourcePair true false
decode t20 = sourcePair true true

decodeEncode : ∀ source → decode (encode source) ≡ source
decodeEncode (sourcePair false false) = refl
decodeEncode (sourcePair false true) = refl
decodeEncode (sourcePair true false) = refl
decodeEncode (sourcePair true true) = refl

encodeDecode : ∀ target → encode (decode target) ≡ target
encodeDecode t00 = refl
encodeDecode t14 = refl
encodeDecode t11 = refl
encodeDecode t20 = refl

------------------------------------------------------------------------
-- Marginal target support versus joint target support.
------------------------------------------------------------------------

data MarginalU : U → Set where
  allowU0 : MarginalU u0
  allowU1 : MarginalU u1
  allowU2 : MarginalU u2

data MarginalV : V → Set where
  allowV0 : MarginalV v0
  allowV1 : MarginalV v1
  allowV4 : MarginalV v4

data JointImage : U → V → Set where
  image00 : JointImage u0 v0
  image14 : JointImage u1 v4
  image11 : JointImage u1 v1
  image20 : JointImage u2 v0

jointCoordinatesReachable : ∀ target → JointImage (uCoord target) (vCoord target)
jointCoordinatesReachable t00 = image00
jointCoordinatesReachable t14 = image14
jointCoordinatesReachable t11 = image11
jointCoordinatesReachable t20 = image20

crossMarginalsEachAllowed : MarginalU u0 × MarginalV v1
crossMarginalsEachAllowed = allowU0 , allowV1

crossMarginalsNotJointlyReachable : JointImage u0 v1 → ⊥
crossMarginalsNotJointlyReachable ()

------------------------------------------------------------------------
-- Exact consequence: the Cartesian product of marginal supports strictly
-- contains pairs not represented by any globally valid transformed state.
------------------------------------------------------------------------

data PriorCouplingWitness : Set where
  targetPriorCoupling : PriorCouplingWitness

priorCouplingWitness : PriorCouplingWitness
priorCouplingWitness = targetPriorCoupling
