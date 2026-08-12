module DASHI.Crypto.InvertibleTransformPriorCouplingRegressionExact where

------------------------------------------------------------------------
-- INVERTIBLE MIXING CAN CREATE TARGET-COORDINATE COUPLING
--
-- Finite exact regression for the NTT prior question.  The source carrier is
-- two independent bits.  An invertible four-state representation change mixes
-- them into two local target coordinates whose marginal supports are larger
-- than the joint image.  Thus local target admissibility does not imply joint
-- admissibility even though the global transform is bijective.
--
-- This is a structural regression, not the FIPS-203 NTT itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record SourcePair : Set where
  constructor sourcePair
  field
    x y : Bool
open SourcePair public

data U : Set where u0 u1 u2 : U
data V : Set where v0 v1 v4 : V

record TargetPair : Set where
  constructor targetPair
  field
    u : U
    v : V
open TargetPair public

-- Images of the four bit pairs under the Z/5-shaped mixing pattern
-- (x,y) |-> (x+y,x-y):
-- 00 -> (0,0), 01 -> (1,4), 10 -> (1,1), 11 -> (2,0).

encode : SourcePair → TargetPair
encode (sourcePair false false) = targetPair u0 v0
encode (sourcePair false true)  = targetPair u1 v4
encode (sourcePair true false)  = targetPair u1 v1
encode (sourcePair true true)   = targetPair u2 v0

decode : TargetPair → SourcePair
decode (targetPair u0 v0) = sourcePair false false
decode (targetPair u0 v1) = sourcePair false false
decode (targetPair u0 v4) = sourcePair false false
decode (targetPair u1 v0) = sourcePair false false
decode (targetPair u1 v1) = sourcePair true false
decode (targetPair u1 v4) = sourcePair false true
decode (targetPair u2 v0) = sourcePair true true
decode (targetPair u2 v1) = sourcePair false false
decode (targetPair u2 v4) = sourcePair false false

-- Exact inverse on the transform image.
decodeEncode : ∀ source → decode (encode source) ≡ source
decodeEncode (sourcePair false false) = refl
decodeEncode (sourcePair false true) = refl
decodeEncode (sourcePair true false) = refl
decodeEncode (sourcePair true true) = refl

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
  image01 : JointImage u1 v4
  image10 : JointImage u1 v1
  image11 : JointImage u2 v0

crossMarginalsEachAllowed : MarginalU u0 × MarginalV v1
crossMarginalsEachAllowed = allowU0 , allowV1
  where
  open import Data.Product using (_×_; _,_)

crossMarginalsNotJointlyReachable : JointImage u0 v1 → ⊥
crossMarginalsNotJointlyReachable ()

------------------------------------------------------------------------
-- This is the finite theorem-shaped warning needed for ML-KEM NTT reasoning:
-- exact/invertible global representation and easy local coordinate predicates
-- do not imply that the transported prior is a Cartesian product.
------------------------------------------------------------------------

data PriorCouplingWitness : Set where
  targetPriorCoupling : PriorCouplingWitness

priorCouplingWitness : PriorCouplingWitness
priorCouplingWitness = targetPriorCoupling
