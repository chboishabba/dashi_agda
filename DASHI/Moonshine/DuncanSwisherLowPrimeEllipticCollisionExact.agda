module DASHI.Moonshine.DuncanSwisherLowPrimeEllipticCollisionExact where

------------------------------------------------------------------------
-- LOW-CHARACTERISTIC COLLISION INSIDE THE DELIGNE / DUNCAN--SWISHER INPUT
--
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Proposition 3.1 treats the two special supersingular J_1 residues
--
--   -744 = 0 - 744,      984 = 1728 - 744
--
-- with different local ramification/sharpness roles: for p>3 the n=1
-- coefficients have exact p-adic depths 3 and 2 respectively.  Table 2 records
-- that at BOTH exceptional characteristics p=2 and p=3 the two residues collapse
-- to the same representative 0.
--
-- The difference is
--
--   984 - (-744) = 1728 = 2^6 * 3^3,
--
-- so the collision is exactly compatible with the exceptional characteristics.
-- The source also explicitly restricts the sharpness statement used downstream
-- to p>3 and notes stronger small-prime bounds.
--
-- DASHI CONTRIBUTION
--
-- Make the collision proof-relevant: the two elliptic roles are distinct, their
-- generic p>3 sharpness weights are distinct, but the low-characteristic residue
-- observer cannot separate them.  This identifies an exact obstruction to a
-- naive p>3 proof transport into p=2,3.
--
-- IMPORTANT BOUNDARY
--
-- This collision is NOT asserted to equal, by itself, the unexplained Monster
-- exponent residuals 10 and 2.  It is a source-native structural place where
-- the p>3 mechanism changes and therefore a concrete target for the missing
-- low-characteristic refinement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Divisibility using (_∣_; divides)

import DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact as Low

data SpecialEllipticRole : Set where
  jZeroRole j1728Role : SpecialEllipticRole

------------------------------------------------------------------------
-- Shifted J_1 values and their exact separation.
------------------------------------------------------------------------

-- J_1=j-744, so the two special values are -744 and 984.  Their Nat separation
-- is 1728; we keep the signed offsets in the source metadata/comments and use
-- the positive separation for exact divisibility arithmetic.
specialJ1Separation : Nat
specialJ1Separation = 1728

specialJ1SeparationFactorisation : specialJ1Separation ≡ 64 * 27
specialJ1SeparationFactorisation = refl

twoDividesSpecialJ1Separation : 2 ∣ specialJ1Separation
twoDividesSpecialJ1Separation = divides 864 refl

threeDividesSpecialJ1Separation : 3 ∣ specialJ1Separation
threeDividesSpecialJ1Separation = divides 576 refl

------------------------------------------------------------------------
-- Source Table 2: both special residue columns are represented by zero in
-- characteristics 2 and 3.
------------------------------------------------------------------------

specialResidueRepresentative :
  Low.DuncanSwisherLowPrime → SpecialEllipticRole → Nat
specialResidueRepresentative Low.low2 jZeroRole = 0
specialResidueRepresentative Low.low2 j1728Role = 0
specialResidueRepresentative Low.low3 jZeroRole = 0
specialResidueRepresentative Low.low3 j1728Role = 0

lowPrimeSpecialResiduesCollide :
  (prime : Low.DuncanSwisherLowPrime) →
  specialResidueRepresentative prime jZeroRole
  ≡ specialResidueRepresentative prime j1728Role
lowPrimeSpecialResiduesCollide Low.low2 = refl
lowPrimeSpecialResiduesCollide Low.low3 = refl

specialEllipticRolesDistinct : jZeroRole ≡ j1728Role → ⊥
specialEllipticRolesDistinct ()

record ExactRoleReconstructionFromLowResidue
    (prime : Low.DuncanSwisherLowPrime) : Set where
  constructor exactRoleReconstructionFromLowResidue
  field
    decode : Nat → SpecialEllipticRole
    exact :
      (role : SpecialEllipticRole) →
      decode (specialResidueRepresentative prime role) ≡ role

open ExactRoleReconstructionFromLowResidue public

lowResidueCannotReconstructEllipticRole :
  (prime : Low.DuncanSwisherLowPrime) →
  ExactRoleReconstructionFromLowResidue prime → ⊥
lowResidueCannotReconstructEllipticRole prime reconstruction =
  specialEllipticRolesDistinct
    (trans
      (sym (exact reconstruction jZeroRole))
      (trans
        (cong (decode reconstruction) (lowPrimeSpecialResiduesCollide prime))
        (exact reconstruction j1728Role)))

------------------------------------------------------------------------
-- The two generic p>3 sharpness roles are genuinely distinct before this
-- low-characteristic residue collapse.
------------------------------------------------------------------------

genericN1SharpnessWeight : SpecialEllipticRole → Nat
genericN1SharpnessWeight jZeroRole = 3
genericN1SharpnessWeight j1728Role = 2

genericSharpnessRolesDiffer :
  genericN1SharpnessWeight jZeroRole
  ≡ genericN1SharpnessWeight j1728Role → ⊥
genericSharpnessRolesDiffer ()

record DuncanSwisherLowPrimeEllipticCollisionBoundary : Set where
  constructor duncanSwisherLowPrimeEllipticCollisionBoundary
  field
    specialJ1ValuesSeparatedBy1728 : Bool
    characteristicsTwoAndThreeDivideSeparation : Bool
    table2SpecialResiduesCollideAtTwoAndThree : Bool
    genericPgt3SharpnessRolesAreDistinct : Bool
    lowResidueObserverReconstructsEllipticRole : Bool
    collisionAloneProvesP2ResidualTen : Bool
    collisionAloneProvesP3ResidualTwo : Bool
    collisionIsConcreteLowCharacteristicObstruction : Bool

canonicalDuncanSwisherLowPrimeEllipticCollisionBoundary :
  DuncanSwisherLowPrimeEllipticCollisionBoundary
canonicalDuncanSwisherLowPrimeEllipticCollisionBoundary =
  duncanSwisherLowPrimeEllipticCollisionBoundary
    true true true true false false false true
