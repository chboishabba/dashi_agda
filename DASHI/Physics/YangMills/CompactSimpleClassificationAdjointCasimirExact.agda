module DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact where

------------------------------------------------------------------------
-- ROUND83: CARTAN--KILLING CLASSIFICATION -> STRICT C_A > 0
--
-- PRIMARY SOURCES
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- N. Bourbaki,
-- "Lie Groups and Lie Algebras, Chapters 4--6", Springer, 2002.
-- ISBN: 978-3-540-69171-6.  No DOI assigned for the cited edition.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- DASHI CONTRIBUTION
--
-- In the long-root-squared-equals-two / SU(2):C_A=2 normalization used by the
-- one-loop modules, the adjoint Casimir is the dual Coxeter number h^vee.
-- `CompactSimpleClassification` already encodes the Cartan--Killing families
-- and their exact h^vee formulas.  Here those formulas are realised as exact
-- rationals and their strict positivity is proved uniformly over every
-- classical and exceptional family.
--
-- Consequently the one-loop frontier must NOT keep "C_A>0 for every compact
-- simple group" as new analysis.  The genuinely physical L1 seam is the
-- literal Wilson/ghost/Haar colour-tensor contraction and its normalization to
-- this classified C_A.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _<_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleClassification as Class
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact as Casimir
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact as Budget

one two three four six nine twelve eighteen thirty : ℚ
one = + 1 / 1
two = + 2 / 1
three = + 3 / 1
four = + 4 / 1
six = + 6 / 1
nine = + 9 / 1
twelve = + 12 / 1
eighteen = + 18 / 1
thirty = + 30 / 1

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = natAsRational n + one

natAsRationalNonnegative : ∀ n → 0ℚ ≤ natAsRational n
natAsRationalNonnegative zero = ℚP.≤-refl
natAsRationalNonnegative (suc n) =
  let
    oneNonnegative : 0ℚ ≤ one
    oneNonnegative = ℚP.nonNegative⁻¹ one
    raw : 0ℚ + 0ℚ ≤ natAsRational n + one
    raw = ℚP.+-mono-≤ (natAsRationalNonnegative n) oneNonnegative
  in
  subst₂ _≤_
    (ℚRing.solve [])
    (ℚRing.solve-∀ (natAsRational n) one)
    raw

positiveOffset : ∀ x c → 0ℚ ≤ x → 0ℚ < c → 0ℚ < x + c
positiveOffset x c xNonnegative cPositive =
  let
    raw : 0ℚ + 0ℚ < c + x
    raw = ℚP.+-mono-<-≤ cPositive xNonnegative
  in
  subst₂ _<_
    (ℚRing.solve [])
    (ℚRing.solve-∀ x c)
    raw

classificationAdjointCasimir : Class.SimpleLieType → ℚ
classificationAdjointCasimir (Class.A n) = natAsRational n + two
classificationAdjointCasimir (Class.B n) =
  (natAsRational n + natAsRational n) + three
classificationAdjointCasimir (Class.C n) = natAsRational n + three
classificationAdjointCasimir (Class.D n) =
  (natAsRational n + natAsRational n) + six
classificationAdjointCasimir Class.E6 = twelve
classificationAdjointCasimir Class.E7 = eighteen
classificationAdjointCasimir Class.E8 = thirty
classificationAdjointCasimir Class.F4 = nine
classificationAdjointCasimir Class.G2 = four

classificationAdjointCasimirPositive :
  ∀ lieType → 0ℚ < classificationAdjointCasimir lieType
classificationAdjointCasimirPositive (Class.A n) =
  positiveOffset (natAsRational n) two
    (natAsRationalNonnegative n) (ℚP.positive⁻¹ two)
classificationAdjointCasimirPositive (Class.B n) =
  positiveOffset
    (natAsRational n + natAsRational n) three
    (ℚP.+-mono-≤
      (natAsRationalNonnegative n)
      (natAsRationalNonnegative n))
    (ℚP.positive⁻¹ three)
classificationAdjointCasimirPositive (Class.C n) =
  positiveOffset (natAsRational n) three
    (natAsRationalNonnegative n) (ℚP.positive⁻¹ three)
classificationAdjointCasimirPositive (Class.D n) =
  positiveOffset
    (natAsRational n + natAsRational n) six
    (ℚP.+-mono-≤
      (natAsRationalNonnegative n)
      (natAsRationalNonnegative n))
    (ℚP.positive⁻¹ six)
classificationAdjointCasimirPositive Class.E6 = ℚP.positive⁻¹ twelve
classificationAdjointCasimirPositive Class.E7 = ℚP.positive⁻¹ eighteen
classificationAdjointCasimirPositive Class.E8 = ℚP.positive⁻¹ thirty
classificationAdjointCasimirPositive Class.F4 = ℚP.positive⁻¹ nine
classificationAdjointCasimirPositive Class.G2 = ℚP.positive⁻¹ four

classificationCasimirCarrier :
  Casimir.CompactSimpleCasimirCarrier Class.SimpleLieType
classificationCasimirCarrier = record
  { Casimir.CompactSimpleCasimirCarrier.adjointCasimir =
      classificationAdjointCasimir
  ; Casimir.CompactSimpleCasimirCarrier.adjointCasimirNonnegative =
      λ lieType → ℚP.<⇒≤ (classificationAdjointCasimirPositive lieType)
  }

classificationStrictCasimirCarrier :
  Budget.StrictCompactSimpleCasimirCarrier Class.SimpleLieType
classificationStrictCasimirCarrier = record
  { Budget.StrictCompactSimpleCasimirCarrier.carrier = classificationCasimirCarrier
  ; Budget.StrictCompactSimpleCasimirCarrier.adjointCasimirPositive =
      classificationAdjointCasimirPositive
  }

su2ClassificationCasimirIsTwo :
  classificationAdjointCasimir Class.su2Type ≡ two
su2ClassificationCasimirIsTwo = refl
  where open import Agda.Builtin.Equality using (_≡_; refl)

classificationAdjointCasimirFormulaLevel : ProofLevel
classificationAdjointCasimirFormulaLevel = machineChecked

classificationAdjointCasimirStrictPositivityLevel : ProofLevel
classificationAdjointCasimirStrictPositivityLevel = machineChecked

classificationToStrictCasimirCarrierLevel : ProofLevel
classificationToStrictCasimirCarrierLevel = machineChecked

-- The remaining group-theoretic physical seam is NOT positivity: it is proving
-- that the colour tensor generated by the literal lattice Wilson, FP ghost and
-- Haar vertices contracts to this classified C_A with the same normalization.
literalWilsonGhostHaarToClassifiedCasimirLevel : ProofLevel
literalWilsonGhostHaarToClassifiedCasimirLevel = conditional
