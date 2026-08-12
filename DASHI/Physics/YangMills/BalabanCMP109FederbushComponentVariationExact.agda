module DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact two-background product telescope needed for the local
-- derivative modulus.  For K(U)=J(U)T(U),
--
--   K(U)-K(V)
--     = [J(U)-J(V)] T(U) + J(V) [T(U)-T(V)].
--
-- The proof is entrywise on the literal three-coordinate SU(2) carrier and
-- uses only finite matrix multiplication and rational ring identities.  It is
-- intentionally upstream of every norm estimate, so the later Lipschitz bound
-- cannot be obtained by differentiating a coarse 1/4 contraction receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component

sumRationalSub :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  sumRational values (λ value → left value - right value)
  ≡ sumRational values left - sumRational values right
sumRationalSub [] left right = ℚRing.solve []
sumRationalSub (value ∷ values) left right
  rewrite sumRationalSub values left right =
  ℚRing.solve-∀
    (left value) (right value)
    (sumRational values left) (sumRational values right)

matrixDifference : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
matrixDifference left right row column = left row column - right row column

composeDifferenceLeft : ∀ left right inner row column →
  Component.matrixCompose (matrixDifference left right) inner row column
  ≡ Component.matrixCompose left inner row column
    - Component.matrixCompose right inner row column
composeDifferenceLeft left right inner row column =
  sumRationalSub Physical.lieCoordinates3
    (λ middle → left row middle * inner middle column)
    (λ middle → right row middle * inner middle column)

composeDifferenceRight : ∀ outer left right row column →
  Component.matrixCompose outer (matrixDifference left right) row column
  ≡ Component.matrixCompose outer left row column
    - Component.matrixCompose outer right row column
composeDifferenceRight outer left right row column =
  trans
    (sumRationalCong
      Physical.lieCoordinates3 _ _
      (λ middle →
        ℚRing.solve-∀
          (outer row middle)
          (left middle column)
          (right middle column)))
    (sumRationalSub Physical.lieCoordinates3
      (λ middle → outer row middle * left middle column)
      (λ middle → outer row middle * right middle column))

componentProductVariationExact :
  ∀ jacobianU transportU jacobianV transportV row column →
  Component.matrixCompose jacobianU transportU row column
    - Component.matrixCompose jacobianV transportV row column
  ≡ Component.matrixCompose
      (matrixDifference jacobianU jacobianV) transportU row column
    + Component.matrixCompose jacobianV
      (matrixDifference transportU transportV) row column
componentProductVariationExact
    jacobianU transportU jacobianV transportV row column =
  trans
    (ℚRing.solve-∀
      (Component.matrixCompose jacobianU transportU row column)
      (Component.matrixCompose jacobianV transportU row column)
      (Component.matrixCompose jacobianV transportV row column))
    (trans
      (cong
        (λ leftTerm →
          leftTerm
          + (Component.matrixCompose jacobianV transportU row column
            - Component.matrixCompose jacobianV transportV row column))
        (symmetry
          (composeDifferenceLeft jacobianU jacobianV transportU row column)))
      (cong
        (Component.matrixCompose
          (matrixDifference jacobianU jacobianV) transportU row column +_)
        (symmetry
          (composeDifferenceRight jacobianV transportU transportV row column))))
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

cmp109FederbushComponentVariationIdentityLevel : ProofLevel
cmp109FederbushComponentVariationIdentityLevel = machineChecked
