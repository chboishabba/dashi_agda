module DASHI.Physics.Closure.NSTriadKNLuoAbuGhuwalehAdditiveFloorNoGoExact where

------------------------------------------------------------------------
-- SOURCE UNDER AUDIT
--
-- Author: Mohammad Abu-Ghuwaleh.
-- Title: "Global Regularity for the Three-Dimensional Periodic
-- Incompressible Navier-Stokes Equations: A Shellwise-Microlocal
-- Modified-Energy Proof".
-- DOI: 10.5281/zenodo.19559087.
-- Status: repository preprint; not used as proof authority.
--
-- AUDITED STEP
--
-- The manuscript combines a dissipative differential inequality for a
-- modified energy with an energy comparison containing a positive additive
-- floor c_J, then states pure exponential decay of the modified energy.
--
-- This file gives an exact finite-step countermodel to that implication.  A
-- zero high-block state and a positive additive floor satisfy:
--
--   E_1 + damping * |V|^2 <= E_0,
--   0 <= E_1,
--   E_1 <= 2 |V|^2 + c,
--
-- with E_0 = E_1 = c = 1 and |V|^2 = 0.  Nevertheless E_1 < E_0 is false.
-- Thus an additive comparison floor cannot be silently discarded when
-- deriving pure decay.  This refutes only the displayed implication; it does
-- not refute every local identity or every possible repaired modified energy.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Nullary.Negation using (¬_)

one : ℚ
one = + 1 / 1

two : ℚ
two = + 2 / 1

counterInitialEnergy : ℚ
counterInitialEnergy = one

counterLaterEnergy : ℚ
counterLaterEnergy = one

counterVelocitySquare : ℚ
counterVelocitySquare = 0ℚ

counterAdditiveFloor : ℚ
counterAdditiveFloor = one

counterDamping : ℚ
counterDamping = one

counterDissipativeStep :
  counterLaterEnergy + counterDamping * counterVelocitySquare
  ≤ counterInitialEnergy
counterDissipativeStep
  rewrite ℚRing.solve [] =
  ℚP.≤-refl

counterLowerComparison :
  0ℚ ≤ counterLaterEnergy
counterLowerComparison =
  ℚP.nonNegative⁻¹ one

counterUpperComparison :
  counterLaterEnergy
  ≤ two * counterVelocitySquare + counterAdditiveFloor
counterUpperComparison
  rewrite ℚRing.solve [] =
  ℚP.≤-refl

pureStrictDecayConclusion : Set
pureStrictDecayConclusion =
  counterLaterEnergy < counterInitialEnergy

pureStrictDecayConclusionFalse :
  ¬ pureStrictDecayConclusion
pureStrictDecayConclusionFalse =
  ℚP.<-irrefl ℚP.≡-refl

record AdditiveFloorNoGoWitness : Set where
  constructor additiveFloorNoGoWitness
  field
    dissipativeStep :
      counterLaterEnergy + counterDamping * counterVelocitySquare
      ≤ counterInitialEnergy
    lowerComparison :
      0ℚ ≤ counterLaterEnergy
    upperComparison :
      counterLaterEnergy
      ≤ two * counterVelocitySquare + counterAdditiveFloor
    strictDecayImpossible :
      ¬ (counterLaterEnergy < counterInitialEnergy)

canonicalAdditiveFloorNoGoWitness : AdditiveFloorNoGoWitness
canonicalAdditiveFloorNoGoWitness =
  additiveFloorNoGoWitness
    counterDissipativeStep
    counterLowerComparison
    counterUpperComparison
    pureStrictDecayConclusionFalse
