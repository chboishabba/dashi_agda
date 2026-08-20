module DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogAdPolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Remove the rational-coefficient mismatch in the older CMP109 Jacobian lane.
-- The actual inverse-dexp Bernoulli coefficient is a Bishop real, so the
-- principal-log differential must not be forced through an ℚ-valued c2 socket.
--
-- On the literal three-dimensional su(2) coordinate carrier define
--
--   J_(c1,beta,X) v
--     = v + c1 [X,v] + beta [X,[X,v]].
--
-- This file proves the exact coefficient telescope directly over Bishop reals:
--
--   J_beta v - J_beta0 v
--     = (beta-beta0) [X,[X,v]].
--
-- The theorem is then specialized to the repository's ACTUAL constructive
-- inverse-dexp coefficient at the CMP109 source radius.  Thus the checked
-- endpoint modulus 0 <= beta-1/12 <= 1/14400 now controls the same Bishop-real
-- operator that enters the printed principal-log derivative.  No rational
-- surrogate for beta is introduced.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanCMP109BishopInverseDexpCoefficientEndpointModulusExact as Endpoint
import DASHI.Physics.YangMills.BalabanCMP109BishopSourceRadiusEndpointExact as Source
open import DASHI.Physics.YangMills.CompactLieProofLevel

record Vec3B : Set where
  constructor vec3B
  field x y z : BishopReal.ℝ
open Vec3B public

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

oneTwelfth : ℚᵘ
oneTwelfth = + 1 / 12

add3 : Vec3B → Vec3B → Vec3B
add3 (vec3B ax ay az) (vec3B bx by bz) =
  vec3B
    (BishopReal._+_ ax bx)
    (BishopReal._+_ ay by)
    (BishopReal._+_ az bz)

sub3 : Vec3B → Vec3B → Vec3B
sub3 (vec3B ax ay az) (vec3B bx by bz) =
  vec3B
    (BishopReal._-_ ax bx)
    (BishopReal._-_ ay by)
    (BishopReal._-_ az bz)

scale3 : BishopReal.ℝ → Vec3B → Vec3B
scale3 scalar (vec3B vx vy vz) =
  vec3B
    (BishopReal._*_ scalar vx)
    (BishopReal._*_ scalar vy)
    (BishopReal._*_ scalar vz)

bracket3 : Vec3B → Vec3B → Vec3B
bracket3 (vec3B x0 x1 x2) (vec3B v0 v1 v2) =
  vec3B
    (BishopReal._-_ (BishopReal._*_ x1 v2) (BishopReal._*_ x2 v1))
    (BishopReal._-_ (BishopReal._*_ x2 v0) (BishopReal._*_ x0 v2))
    (BishopReal._-_ (BishopReal._*_ x0 v1) (BishopReal._*_ x1 v0))

adSquare3 : Vec3B → Vec3B → Vec3B
adSquare3 generator value = bracket3 generator (bracket3 generator value)

principalLogAdApply :
  BishopReal.ℝ → BishopReal.ℝ → Vec3B → Vec3B → Vec3B
principalLogAdApply c1 beta generator value =
  add3 value
    (add3
      (scale3 c1 (bracket3 generator value))
      (scale3 beta (adSquare3 generator value)))

vec3Congruent : Vec3B → Vec3B → Set
vec3Congruent left right =
  BishopReal._≃_ (x left) (x right)
  × (BishopReal._≃_ (y left) (y right)
    × BishopReal._≃_ (z left) (z right))

principalLogCoefficientTelescope :
  ∀ c1 beta beta0 generator value →
  vec3Congruent
    (sub3
      (principalLogAdApply c1 beta generator value)
      (principalLogAdApply c1 beta0 generator value))
    (scale3 (BishopReal._-_ beta beta0) (adSquare3 generator value))
principalLogCoefficientTelescope c1 beta beta0
    (vec3B x0 x1 x2) (vec3B v0 v1 v2) =
  (let open BishopProperties.ℝ-Solver
   in solve 9
     (λ c b b0 x0 x1 x2 v0 v1 v2 →
       let
         a0 = (x1 ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0))
              ⊖ (x2 ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2))
       in
       ((v0 ⊕ ((c ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1)) ⊕ (b ⊗ a0)))
        ⊖ (v0 ⊕ ((c ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1)) ⊕ (b0 ⊗ a0))))
       ⊜ ((b ⊖ b0) ⊗ a0))
     BishopProperties.≃-refl
     c1 beta beta0 x0 x1 x2 v0 v1 v2)
  ,
  ((let open BishopProperties.ℝ-Solver
    in solve 9
      (λ c b b0 x0 x1 x2 v0 v1 v2 →
        let
          a1 = (x2 ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1))
               ⊖ (x0 ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0))
        in
        ((v1 ⊕ ((c ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2)) ⊕ (b ⊗ a1)))
         ⊖ (v1 ⊕ ((c ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2)) ⊕ (b0 ⊗ a1))))
        ⊜ ((b ⊖ b0) ⊗ a1))
      BishopProperties.≃-refl
      c1 beta beta0 x0 x1 x2 v0 v1 v2)
   ,
   (let open BishopProperties.ℝ-Solver
    in solve 9
      (λ c b b0 x0 x1 x2 v0 v1 v2 →
        let
          a2 = (x0 ⊗ (x2 ⊗ v0 ⊖ x0 ⊗ v2))
               ⊖ (x1 ⊗ (x1 ⊗ v2 ⊖ x2 ⊗ v1))
        in
        ((v2 ⊕ ((c ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0)) ⊕ (b ⊗ a2)))
         ⊖ (v2 ⊕ ((c ⊗ (x0 ⊗ v1 ⊖ x1 ⊗ v0)) ⊕ (b0 ⊗ a2))))
        ⊜ ((b ⊖ b0) ⊗ a2))
      BishopProperties.≃-refl
      c1 beta beta0 x0 x1 x2 v0 v1 v2))

actualSourceInverseDexpCoefficient :
  ∀ {dataSet} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet Source.sourceRadiusValue →
  BishopReal.ℝ
actualSourceInverseDexpCoefficient inputs =
  Positive.inverseDexpCoefficientPositive inputs Source.sourceRadiusPositive

actualSourcePrincipalLogCoefficientTelescope :
  ∀ {dataSet}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs
      dataSet Source.sourceRadiusValue)
    c1 generator value →
  vec3Congruent
    (sub3
      (principalLogAdApply c1
        (actualSourceInverseDexpCoefficient inputs) generator value)
      (principalLogAdApply c1 (embed oneTwelfth) generator value))
    (scale3
      (Endpoint.coefficientEndpointDefect inputs Source.sourceRadiusPositive)
      (adSquare3 generator value))
actualSourcePrincipalLogCoefficientTelescope inputs c1 generator value =
  principalLogCoefficientTelescope
    c1
    (actualSourceInverseDexpCoefficient inputs)
    (embed oneTwelfth)
    generator value

cmp109BishopPrincipalLogAdPolynomialLevel : ProofLevel
cmp109BishopPrincipalLogAdPolynomialLevel = machineChecked

cmp109BishopActualCoefficientSameOperatorLevel : ProofLevel
cmp109BishopActualCoefficientSameOperatorLevel = machineChecked

-- The remaining CMP109 seam is now only identification of this literal
-- Bishop-real ad-polynomial with the paper's chosen left/right trivialized
-- product derivative.  The coefficient and its source-radius modulus are on
-- the correct carrier already.
cmp109PrintedBishopAdPolynomialTrivializationLevel : ProofLevel
cmp109PrintedBishopAdPolynomialTrivializationLevel = conditional
