{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechSignedWeightedMixtureActionExact where

-- A real *sign-valued* arbitrary-E weighted-mixture theorem, not the
-- Nat-only sum that cannot express geometric inversion.
-- The carrier may be instantiated with exact rationals/reals/vectors.
-- The algebraic laws are explicit; no type is silently treated as ℝ.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record SignedWeightedCarrier : Set₁ where
  field
    Scalar : Set
    Vector : Set
    zero : Vector
    add : Vector → Vector → Vector
    scale : Scalar → Vector → Vector
    negative : Vector → Vector
    negativeZero : negative zero ≡ zero
    negativeAdd :
      (x y : Vector) → negative (add x y) ≡
                       add (negative x) (negative y)
    negativeScale :
      (w : Scalar) (x : Vector) →
      negative (scale w x) ≡ scale w (negative x)

module Transport (M : SignedWeightedCarrier) where
  open SignedWeightedCarrier M

  routeMap : ∀ {E : Nat} →
             (Fin E → Fin E) → List (Fin E) → List (Fin E)
  routeMap permutation [] = []
  routeMap permutation (e ∷ rest) =
    permutation e ∷ routeMap permutation rest

  mixture : ∀ {E : Nat} →
            List (Fin E) →
            (Fin E → Scalar) →
            (Fin E → Vector) → Vector
  mixture [] weights outputs = zero
  mixture (e ∷ rest) weights outputs =
    add (scale (weights e) (outputs e))
        (mixture rest weights outputs)

  -- The action transforms selected IDs, scalar weights, and expert
  -- outputs. A true expert permutation must additionally certify a
  -- two-sided inverse and no duplicate selected IDs.
  entireMixtureIsOdd :
    ∀ {E : Nat}
    (selected : List (Fin E))
    (p : Fin E → Fin E)
    (w w' : Fin E → Scalar)
    (y y' : Fin E → Vector) →
    ((e : Fin E) → w' (p e) ≡ w e) →
    ((e : Fin E) → y' (p e) ≡ negative (y e)) →
    mixture (routeMap p selected) w' y'
       ≡ negative (mixture selected w y)
  entireMixtureIsOdd [] p w w' y y' weightLaw outputLaw =
    sym negativeZero
  entireMixtureIsOdd (e ∷ rest) p w w' y y' weightLaw outputLaw
    rewrite weightLaw e
          | outputLaw e
          | entireMixtureIsOdd rest p w w' y y' weightLaw outputLaw
          | negativeAdd (scale (w e) (y e))
                        (mixture rest w y)
          | negativeScale (w e) (y e) = refl

-- Cross-reference the separately proved all-E history updater
-- LeechGenericHistoryActionTransportExact. Combined output/history
-- equivariance is conditional on router, weights and update laws.
-- Nothing above treats an opposing argument as a geometric antipode.
