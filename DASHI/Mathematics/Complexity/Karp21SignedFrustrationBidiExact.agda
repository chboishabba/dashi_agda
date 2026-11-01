module DASHI.Mathematics.Complexity.Karp21SignedFrustrationBidiExact where

------------------------------------------------------------------------
-- TWO DISTINCT SIGNED GRAPH OPTIMIZATION OWNERS, EXACTLY RELATED:
--
-- (1) Karp (1972) SIGNED MAX CUT: maximize Σ w_e [bits differ].
--     A negative w penalizes crossing, NOT repulsion/reward-to-separate.
--
-- (2) Signed correlation clustering / structural-balance frustration:
--     minimize Σ positiveMagnitude_e [bits differ]
--            + Σ negativeMagnitude_e [bits equal].
--     Here a negative edge prefers different sides.
--
-- The exact AFFINE bridge for every Boolean bipartition is
--     frustration(E,b) = signedCut(E,b) + Σ negativeMagnitude(E).
-- Thus maximizing signedCut is maximizing, NOT minimizing, frustration.
-- Signed PSD corrected-gap energy = 4*frustration in the Boolean domain.
--
-- Prior art: Cartwright/Harary balance (1950s), Kunegis et al. (2010)
-- signed Laplacian; distinct from Karp 1972 decision optimization.
-- PNF signed severity/frustration: Interop.PNFSignedResidualDelta0Exact.
-- This is source-written, not yet an Agda kernel certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import Data.Vec.Base as Vec
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

negativeMagnitude : ℤ → ℤ
negativeMagnitude (+ n) = + 0
negativeMagnitude (-[1+ n ]) = + (suc n)

positiveMagnitude : ℤ → ℤ
positiveMagnitude (+ n) = + n
positiveMagnitude (-[1+ n ]) = + 0

frustrationEdge : ℤ → Bool → Bool → ℤ
frustrationEdge (+ n) true true = + 0
frustrationEdge (+ n) false false = + 0
frustrationEdge (+ n) true false = + n
frustrationEdge (+ n) false true = + n
frustrationEdge (-[1+ n ]) true true = + (suc n)
frustrationEdge (-[1+ n ]) false false = + (suc n)
frustrationEdge (-[1+ n ]) true false = + 0
frustrationEdge (-[1+ n ]) false true = + 0

plusZero : (w : ℤ) → w + (+ 0) ≡ w
plusZero w =
  RingZ.solve 1 (λ x → (x ⊕ Κ (+ 0) , x)) refl w

zeroPlus : (w : ℤ) → (+ 0) + w ≡ w
zeroPlus w =
  RingZ.solve 1 (λ x → (Κ (+ 0) ⊕ x , x)) refl w

minusCancel : (w : ℤ) → (- w) + w ≡ + 0
minusCancel w =
  RingZ.solve 1
    (λ x → ((⊝ x) ⊕ x , Κ (+ 0))) refl w

signedCutPlusNegativeMagnitudeEqualsFrustrationEdge :
  (w : ℤ) (a b : Bool) →
  Lap.bitCutWeight w a b + negativeMagnitude w ≡
  frustrationEdge w a b
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (+ n) true true = refl
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (+ n) false false = refl
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (+ n) true false =
  plusZero (+ n)
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (+ n) false true =
  plusZero (+ n)
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (-[1+ n ]) true true =
  zeroPlus (+ (suc n))
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (-[1+ n ]) false false =
  zeroPlus (+ (suc n))
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (-[1+ n ]) true false =
  minusCancel (+ (suc n))
signedCutPlusNegativeMagnitudeEqualsFrustrationEdge (-[1+ n ]) false true =
  minusCancel (+ (suc n))

-- This is the *positive-semidefinite signed graph* quadratic at ±1
-- spins, D_|W|-W, NOT the indefinite incidence operator B^T W B.
signedPSDSpinEnergyEdge : ℤ → Bool → Bool → ℤ
signedPSDSpinEnergyEdge (+ n) a b =
  (+ n) * Lap.spinGapSquare a b
signedPSDSpinEnergyEdge (-[1+ n ]) a b =
  (+ (suc n)) *
    ((Lap.spin a + Lap.spin b) * (Lap.spin a + Lap.spin b))

fourFrustrationEqualsSignedPSDSpinEdge :
  (w : ℤ) (a b : Bool) →
  (+ 4) * frustrationEdge w a b ≡
  signedPSDSpinEnergyEdge w a b
fourFrustrationEqualsSignedPSDSpinEdge (+ n) true true =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ Κ (+ 0) , x ⊗ Κ (+ 0))) refl (+ n)
fourFrustrationEqualsSignedPSDSpinEdge (+ n) false false =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ Κ (+ 0) , x ⊗ Κ (+ 0))) refl (+ n)
fourFrustrationEqualsSignedPSDSpinEdge (+ n) true false =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ x , x ⊗ Κ (+ 4))) refl (+ n)
fourFrustrationEqualsSignedPSDSpinEdge (+ n) false true =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ x , x ⊗ Κ (+ 4))) refl (+ n)
fourFrustrationEqualsSignedPSDSpinEdge (-[1+ n ]) true true =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ x , x ⊗ Κ (+ 4))) refl (+ (suc n))
fourFrustrationEqualsSignedPSDSpinEdge (-[1+ n ]) false false =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ x , x ⊗ Κ (+ 4))) refl (+ (suc n))
fourFrustrationEqualsSignedPSDSpinEdge (-[1+ n ]) true false =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ Κ (+ 0) , x ⊗ Κ (+ 0))) refl (+ (suc n))
fourFrustrationEqualsSignedPSDSpinEdge (-[1+ n ]) false true =
  RingZ.solve 1 (λ x → (Κ (+ 4) ⊗ Κ (+ 0) , x ⊗ Κ (+ 0))) refl (+ (suc n))

negativeMagnitudeSum :
  ∀ {n : Nat} → List (Cut.SignedUndirectedEdge n) → ℤ
negativeMagnitudeSum [] = + 0
negativeMagnitudeSum (e ∷ es) =
  negativeMagnitude (Cut.weight e) + negativeMagnitudeSum es

frustrationValue :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec Bool n → ℤ
frustrationValue [] labels = + 0
frustrationValue (e ∷ es) labels =
  frustrationEdge (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
  + frustrationValue es labels

signedPSDSpinEnergy :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec Bool n → ℤ
signedPSDSpinEnergy [] labels = + 0
signedPSDSpinEnergy (e ∷ es) labels =
  signedPSDSpinEnergyEdge (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
  + signedPSDSpinEnergy es labels

addReassociate : (a b c d : ℤ) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
addReassociate a b c d =
  RingZ.solve 4
    (λ a b c d →
      ((a ⊕ b) ⊕ (c ⊕ d)
      , (a ⊕ c) ⊕ (b ⊕ d)))
    refl a b c d

-- All finite graphs, including duplicate and signed negative edges.
signedMaxCutFrustrationAffineBidi :
  ∀ {n : Nat}
    (es : List (Cut.SignedUndirectedEdge n))
    (bits : Vec.Vec Bool n) →
  Cut.edgeListCutValue es bits + negativeMagnitudeSum es
  ≡ frustrationValue es bits
signedMaxCutFrustrationAffineBidi [] bits = refl
signedMaxCutFrustrationAffineBidi (e ∷ es) bits =
  trans
    (addReassociate
      (Cut.edgeContribution e bits)
      (Cut.edgeListCutValue es bits)
      (negativeMagnitude (Cut.weight e))
      (negativeMagnitudeSum es))
    (cong₂ _+_
      (trans
        (cong
          (λ value → value + negativeMagnitude (Cut.weight e))
          (Lap.edgeContributionMatchesBitCut e bits))
        (signedCutPlusNegativeMagnitudeEqualsFrustrationEdge
          (Cut.weight e)
          (Vec.lookup bits (Cut.first e))
          (Vec.lookup bits (Cut.second e))))
      (signedMaxCutFrustrationAffineBidi es bits))

fourDistributesOverSum : (a b : ℤ) →
  (+ 4) * (a + b) ≡ (+ 4) * a + (+ 4) * b
fourDistributesOverSum = Lap.fourDistributesOverSum

signedPSDEnergyEqualsFourFrustration :
  ∀ {n : Nat}
    (es : List (Cut.SignedUndirectedEdge n))
    (bits : Vec.Vec Bool n) →
  (+ 4) * frustrationValue es bits ≡
  signedPSDSpinEnergy es bits
signedPSDEnergyEqualsFourFrustration [] bits = refl
signedPSDEnergyEqualsFourFrustration (e ∷ es) bits =
  trans
    (fourDistributesOverSum
      (frustrationEdge (Cut.weight e)
        (Vec.lookup bits (Cut.first e))
        (Vec.lookup bits (Cut.second e)))
      (frustrationValue es bits))
    (cong₂ _+_
      (fourFrustrationEqualsSignedPSDSpinEdge
        (Cut.weight e)
        (Vec.lookup bits (Cut.first e))
        (Vec.lookup bits (Cut.second e)))
      (signedPSDEnergyEqualsFourFrustration es bits))

signedPSDSpinIsAffineMaxCutScore :
  ∀ {n : Nat}
    (es : List (Cut.SignedUndirectedEdge n))
    (bits : Vec.Vec Bool n) →
  signedPSDSpinEnergy es bits ≡
  (+ 4) * (Cut.edgeListCutValue es bits + negativeMagnitudeSum es)
signedPSDSpinIsAffineMaxCutScore es bits =
  trans
    (sym (signedPSDEnergyEqualsFourFrustration es bits))
    (sym (cong (λ x → (+ 4) * x)
      (signedMaxCutFrustrationAffineBidi es bits)))
