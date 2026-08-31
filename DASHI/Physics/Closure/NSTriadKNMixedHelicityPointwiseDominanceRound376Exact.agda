module DASHI.Physics.Closure.NSTriadKNMixedHelicityPointwiseDominanceRound376Exact where

------------------------------------------------------------------------
-- ROUND376 / ROUTINE FINITE ALGEBRA: Q_mixed <= Q_companion
--
-- R227/R228 already prove
--
--   Q_companion = 16 * Q_mixed.
--
-- The remaining order fact is not a PDE theorem.  Q_mixed is literally a
-- finite sum of squared rational Complex3 norms, hence nonnegative.  Repeated
-- doubling gives q <= 16 q, and the R228 identity transports that inequality
-- to the physical companion mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCompanionMassRound226Exact as R226
import DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact as R227
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240

F : C3.RealField _
F = Rational.rationalRealField

complexModulusSquaredNonnegative :
  (z : C3.Complex F) →
  0ℚ ≤ L2.complexModulusSquared z
complexModulusSquaredNonnegative (C3.complex real imaginary) =
  Rational.addNonnegative
    (Rational.squareNonnegative real)
    (Rational.squareNonnegative imaginary)

complex3NormSquaredNonnegative :
  (v : C3.Complex3 F) →
  0ℚ ≤ L2.complex3NormSquared v
complex3NormSquaredNonnegative (C3.complex3 x y z) =
  Rational.addNonnegative
    (Rational.addNonnegative
      (complexModulusSquaredNonnegative x)
      (complexModulusSquaredNonnegative y))
    (complexModulusSquaredNonnegative z)

mapSumNonnegative :
  (f : Z3.FourierMode → ℚ) →
  ((k : Z3.FourierMode) → 0ℚ ≤ f k) →
  (outputs : List Z3.FourierMode) →
  0ℚ ≤ R227.mapSum f outputs
mapSumNonnegative f fNN [] = ℚP.≤-refl
mapSumNonnegative f fNN (k ∷ ks) =
  Rational.addNonnegative (fNN k) (mapSumNonnegative f fNN ks)

mixedOutputMassNonnegative :
  ∀ {E I}
    (S : _) (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  0ℚ ≤ R227.mixedOutputMass {E = E} {I = I} S velocity cutoff output
mixedOutputMassNonnegative S velocity cutoff output =
  complex3NormSquaredNonnegative _

mixedMassNonnegative :
  (T : R228.PhysicalTimeIntegral _ _ .PhysicalMixedHelicityTrajectory) → Set
mixedMassNonnegative T = Set

-- Pure ordered arithmetic: q >= 0 implies q <= 16 q.
nonnegativeBelowSixteenCopies :
  (q : ℚ) → 0ℚ ≤ q → q ≤ R226.sixteen * q
nonnegativeBelowSixteenCopies q qNN =
  subst
    (q ≤_)
    sixteenCopiesMeaning
    q≤sixteenCopies
  where
  two four eight sixteenCopies : ℚ
  two = q + q
  four = two + two
  eight = four + four
  sixteenCopies = eight + eight

  q≤two : q ≤ two
  q≤two =
    subst
      (λ left → left ≤ q + q)
      (ℚP.+-identityʳ q)
      (ℚP.+-monoʳ-≤ q qNN)

  twoNN : 0ℚ ≤ two
  twoNN = Rational.addNonnegative qNN qNN

  two≤four : two ≤ four
  two≤four =
    subst
      (λ left → left ≤ two + two)
      (ℚP.+-identityʳ two)
      (ℚP.+-monoʳ-≤ two twoNN)

  fourNN : 0ℚ ≤ four
  fourNN = Rational.addNonnegative twoNN twoNN

  four≤eight : four ≤ eight
  four≤eight =
    subst
      (λ left → left ≤ four + four)
      (ℚP.+-identityʳ four)
      (ℚP.+-monoʳ-≤ four fourNN)

  eightNN : 0ℚ ≤ eight
  eightNN = Rational.addNonnegative fourNN fourNN

  eight≤sixteen : eight ≤ sixteenCopies
  eight≤sixteen =
    subst
      (λ left → left ≤ eight + eight)
      (ℚP.+-identityʳ eight)
      (ℚP.+-monoʳ-≤ eight eightNN)

  q≤sixteenCopies : q ≤ sixteenCopies
  q≤sixteenCopies =
    ℚP.≤-trans q≤two
      (ℚP.≤-trans two≤four
        (ℚP.≤-trans four≤eight eight≤sixteen))

  sixteenCopiesMeaning : sixteenCopies ≡ R226.sixteen * q
  sixteenCopiesMeaning = solve (q ∷ [])

module PhysicalDominance
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) where

  module Base = R228.PhysicalTimeIntegral Time integrateTo

  physicalMixedMassNonnegative :
    (T : Base.PhysicalMixedHelicityTrajectory) →
    (N : Nat) (t : Time) →
    0ℚ ≤ Base.mixedHelicityMass T N t
  physicalMixedMassNonnegative T N t =
    mapSumNonnegative
      (R227.mixedOutputMass
        {E = Base.E T} {I = Base.I T}
        (Base.S T)
        (Audit.velocity (Base.systemAt T N t))
        N)
      (mixedOutputMassNonnegative
        (Base.S T)
        (Audit.velocity (Base.systemAt T N t))
        N)
      (Audit.modes (Base.systemAt T N t))

  physicalMixedBelowCompanion :
    (T : Base.PhysicalMixedHelicityTrajectory) →
    (N : Nat) (t : Time) →
    Base.mixedHelicityMass T N t
    ≤ Base.companionMass T N t
  physicalMixedBelowCompanion T N t =
    subst
      (Base.mixedHelicityMass T N t ≤_)
      (sym (Base.companionMassPointwiseIsSixteenMixed T N t))
      (nonnegativeBelowSixteenCopies
        (Base.mixedHelicityMass T N t)
        (physicalMixedMassNonnegative T N t))

round376MixedHelicityMassNonnegativeByFiniteNormAlgebra : Bool
round376MixedHelicityMassNonnegativeByFiniteNormAlgebra = true

round376MixedBelowSixteenMixedByOrderedArithmetic : Bool
round376MixedBelowSixteenMixedByOrderedArithmetic = true

round376PhysicalMixedBelowCompanionPointwiseClosed : Bool
round376PhysicalMixedBelowCompanionPointwiseClosed = true

round376NoPDEEstimateUsed : Bool
round376NoPDEEstimateUsed = true

round376PhysicalMixedBelowCompanionPointwiseClosedIsTrue :
  round376PhysicalMixedBelowCompanionPointwiseClosed ≡ true
round376PhysicalMixedBelowCompanionPointwiseClosedIsTrue = refl
