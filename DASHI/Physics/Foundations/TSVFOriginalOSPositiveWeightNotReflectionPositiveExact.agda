{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalOSPositiveWeightNotReflectionPositiveExact where

-- HIL07/S10: finite exact falsification control.
--
-- A strictly positive probability weight on a configuration space
-- does NOT alone entail Osterwalder--Schrader reflection positivity.
-- A two-point reflected support with the swap theta and the
-- antisymmetric test F has a negative reflected quadratic integrand
-- at BOTH configurations.
--
-- Consequently the YM donor's actual R445 native OS pullback still
-- needs genuine fine Wilson RP and a reflection-intertwining,
-- positive-time cylinder algebra; positivity of an effective density
-- is insufficient. This is not a counterexample to Wilson RP on
-- its correctly selected physical reflection plane.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Sign : Set where
  positive negative : Sign

signMultiply : Sign → Sign → Sign
signMultiply positive positive = positive
signMultiply positive negative = negative
signMultiply negative positive = negative
signMultiply negative negative = positive

-- The two configurations have positive (unit) probability weights.
-- The selected reflection exchanges them.
reflect : Bool → Bool
reflect true = false
reflect false = true

reflectionInvolutive : (x : Bool) → reflect (reflect x) ≡ x
reflectionInvolutive true = refl
reflectionInvolutive false = refl

oddObservable : Bool → Sign
oddObservable true = positive
oddObservable false = negative

reflectedProduct : Bool → Sign
reflectedProduct x =
  signMultiply (oddObservable (reflect x)) (oddObservable x)

reflectedProductAlwaysNegative :
  (x : Bool) → reflectedProduct x ≡ negative
reflectedProductAlwaysNegative true = refl
reflectedProductAlwaysNegative false = refl

-- This physically material counterexample is not a Boolean phantom
-- "status flag": each actual configuration's reflected integrand
-- is explicitly the negative sign, and the reflection is involutive.
--
-- With the ordinary normalized uniform measure 1/2+1/2,
-- the real-valued OS form is -1, not >=0.
-- The arithmetic on chosen real scalars is deliberately left to
-- RealAnalysisAxioms, not smuggled into this safe sign-level file.
noPointwisePositiveReflectedProduct :
  (x : Bool) → reflectedProduct x ≡ positive → ⊥
noPointwisePositiveReflectedProduct true ()
noPointwisePositiveReflectedProduct false ()
