module DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Give the source-faithful noncommutative product telescope for an arbitrary
-- CMP109 contour.  For two equal-length ordered quaternion paths U and V,
--
--   prod(U) - prod(V)
--
-- is expanded recursively with exactly one link difference in every term:
--
--   (U0-V0) prod(Utail)
--     + V0 (prod(Utail)-prod(Vtail)).
--
-- Iterating gives the usual ordered path telescope without assuming
-- commutativity.  This is the correct upstream object for the two-background
-- transport modulus: bond differences -> path-product difference -> adjoint
-- transport difference.  No matrix perturbation theorem is inserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Four

pathProduct : List Q.RationalQuaternion → Q.RationalQuaternion
pathProduct [] = Q.oneQ
pathProduct (factor ∷ factors) = factor Q.*q pathProduct factors

pathDifferenceTelescope :
  List Q.RationalQuaternion → List Q.RationalQuaternion → Q.RationalQuaternion
pathDifferenceTelescope [] [] = Q.zeroQ
pathDifferenceTelescope [] (_ ∷ _) = Q.zeroQ
pathDifferenceTelescope (_ ∷ _) [] = Q.zeroQ
pathDifferenceTelescope (u ∷ us) (v ∷ vs) =
  ((Four._-q_ u v) Q.*q pathProduct us)
  Q.+q
  (v Q.*q pathDifferenceTelescope us vs)

oneStepProductDifferenceExact : ∀ a b p q →
  Four._-q_ (a Q.*q p) (b Q.*q q)
  ≡ ((Four._-q_ a b) Q.*q p)
    Q.+q (b Q.*q (Four._-q_ p q))
oneStepProductDifferenceExact
    (Q.quat a0 a1 a2 a3)
    (Q.quat b0 b1 b2 b3)
    (Q.quat p0 p1 p2 p3)
    (Q.quat q0 q1 q2 q3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3 q0 q1 q2 q3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 p2 p3 q0 q1 q2 q3)

sucInjective : ∀ {m n : Nat} → suc m ≡ suc n → m ≡ n
sucInjective refl = refl

pathProductDifferenceTelescopeExact :
  ∀ left right →
  length left ≡ length right →
  Four._-q_ (pathProduct left) (pathProduct right)
  ≡ pathDifferenceTelescope left right
pathProductDifferenceTelescopeExact [] [] refl =
  Q.quaternionExt
    (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve [])
pathProductDifferenceTelescopeExact [] (_ ∷ _) ()
pathProductDifferenceTelescopeExact (_ ∷ _) [] ()
pathProductDifferenceTelescopeExact (u ∷ us) (v ∷ vs) lengthEqual =
  trans
    (oneStepProductDifferenceExact
      u v (pathProduct us) (pathProduct vs))
    (cong
      (λ tailDifference →
        ((Four._-q_ u v) Q.*q pathProduct us)
        Q.+q (v Q.*q tailDifference))
      (pathProductDifferenceTelescopeExact us vs
        (sucInjective lengthEqual)))

cmp109QuaternionPathProductTelescopeLevel : ProofLevel
cmp109QuaternionPathProductTelescopeLevel = machineChecked
