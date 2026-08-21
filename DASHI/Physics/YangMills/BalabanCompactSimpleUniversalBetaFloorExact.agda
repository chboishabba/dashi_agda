module DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact where

------------------------------------------------------------------------
-- ROUND85: ONE GROUP-INDEPENDENT POSITIVE-BETA REMAINDER THRESHOLD
--
-- SOURCES / NORMALIZATION
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
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
-- Round84 already classified every compact-simple adjoint Casimir in the
-- long-root-squared-two normalization and proved C_A>0.  The formulas actually
-- give the stronger UNIFORM floor
--
--                       2 <= C_A(G).
--
-- Since the universal pure-YM scalar is 11/24, every classified compact-simple
-- group therefore obeys
--
--                  11/12 <= C_A(G) * 11/24.
--
-- Thus a single literal same-object regular-remainder enclosure R < 11/12 is
-- sufficient to lie below the universal one-loop coefficient for EVERY compact
-- simple group.  No Dynkin-family-specific remainder threshold is needed.
--
-- This does not prove the physical Wilson+reduced-FP+Haar remainder estimate.
-- It removes group-dependent arithmetic from that remaining L1 theorem.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleClassification as Class
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Classified
import DASHI.Physics.YangMills.BalabanCompactSimpleOneLoopRemainderBudgetExact as Budget

universalCompactSimpleCasimirFloor : ℚ
universalCompactSimpleCasimirFloor = + 2 / 1

universalCompactSimpleBetaFloor : ℚ
universalCompactSimpleBetaFloor = + 11 / 12

universalScalarNonnegative : 0ℚ ≤ Budget.universalScalarCoefficient
universalScalarNonnegative = ℚP.<⇒≤ Budget.universalScalarCoefficientPositive

private
  twoBelowOffset :
    ∀ x c →
    0ℚ ≤ x →
    0ℚ ≤ c - universalCompactSimpleCasimirFloor →
    universalCompactSimpleCasimirFloor ≤ x + c
  twoBelowOffset x c xNonnegative gapNonnegative =
    let
      floorBelowC0 :
        0ℚ + universalCompactSimpleCasimirFloor
        ≤ (c - universalCompactSimpleCasimirFloor)
          + universalCompactSimpleCasimirFloor
      floorBelowC0 = ℚP.+-mono-≤ gapNonnegative ℚP.≤-refl

      floorBelowC : universalCompactSimpleCasimirFloor ≤ c
      floorBelowC = subst₂ _≤_
        (ℚRing.solve-∀ universalCompactSimpleCasimirFloor)
        (ℚRing.solve-∀ c universalCompactSimpleCasimirFloor)
        floorBelowC0

      raw :
        0ℚ + universalCompactSimpleCasimirFloor ≤ x + c
      raw = ℚP.+-mono-≤ xNonnegative floorBelowC
    in
    subst₂ _≤_
      (ℚRing.solve-∀ universalCompactSimpleCasimirFloor)
      (ℚRing.solve-∀ x c)
      raw

classificationAdjointCasimirAtLeastTwo :
  ∀ lieType →
  universalCompactSimpleCasimirFloor
  ≤ Classified.classificationAdjointCasimir lieType
classificationAdjointCasimirAtLeastTwo (Class.A n) =
  twoBelowOffset
    (Classified.natAsRational n)
    Classified.two
    (Classified.natAsRationalNonnegative n)
    (ℚP.nonNegative⁻¹ (Classified.two - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo (Class.B n) =
  twoBelowOffset
    (Classified.natAsRational n + Classified.natAsRational n)
    Classified.three
    (ℚP.+-mono-≤
      (Classified.natAsRationalNonnegative n)
      (Classified.natAsRationalNonnegative n))
    (ℚP.nonNegative⁻¹ (Classified.three - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo (Class.C n) =
  twoBelowOffset
    (Classified.natAsRational n)
    Classified.three
    (Classified.natAsRationalNonnegative n)
    (ℚP.nonNegative⁻¹ (Classified.three - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo (Class.D n) =
  twoBelowOffset
    (Classified.natAsRational n + Classified.natAsRational n)
    Classified.six
    (ℚP.+-mono-≤
      (Classified.natAsRationalNonnegative n)
      (Classified.natAsRationalNonnegative n))
    (ℚP.nonNegative⁻¹ (Classified.six - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo Class.E6 =
  twoBelowOffset 0ℚ Classified.twelve ℚP.≤-refl
    (ℚP.nonNegative⁻¹ (Classified.twelve - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo Class.E7 =
  twoBelowOffset 0ℚ Classified.eighteen ℚP.≤-refl
    (ℚP.nonNegative⁻¹ (Classified.eighteen - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo Class.E8 =
  twoBelowOffset 0ℚ Classified.thirty ℚP.≤-refl
    (ℚP.nonNegative⁻¹ (Classified.thirty - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo Class.F4 =
  twoBelowOffset 0ℚ Classified.nine ℚP.≤-refl
    (ℚP.nonNegative⁻¹ (Classified.nine - universalCompactSimpleCasimirFloor))
classificationAdjointCasimirAtLeastTwo Class.G2 =
  twoBelowOffset 0ℚ Classified.four ℚP.≤-refl
    (ℚP.nonNegative⁻¹ (Classified.four - universalCompactSimpleCasimirFloor))

classificationGroupUniversalCoefficientAtLeastElevenTwelfths :
  ∀ lieType →
  universalCompactSimpleBetaFloor
  ≤ Budget.groupUniversalCoefficient
      Classified.classificationStrictCasimirCarrier lieType
classificationGroupUniversalCoefficientAtLeastElevenTwelfths lieType =
  let
    ca = Classified.classificationAdjointCasimir lieType
    scaled :
      universalCompactSimpleCasimirFloor * Budget.universalScalarCoefficient
      ≤ ca * Budget.universalScalarCoefficient
    scaled =
      ℚP.*-monoʳ-≤-nonNeg
        Budget.universalScalarCoefficient
        (classificationAdjointCasimirAtLeastTwo lieType)
  in
  subst₂ _≤_
    (ℚRing.solve [])
    (ℚRing.solve-∀ ca)
    scaled

uniformRemainderBelowEveryCompactSimpleCoefficient :
  ∀ radius lieType →
  radius < universalCompactSimpleBetaFloor →
  radius < Budget.groupUniversalCoefficient
      Classified.classificationStrictCasimirCarrier lieType
uniformRemainderBelowEveryCompactSimpleCoefficient radius lieType radiusBelowFloor =
  ℚP.<-≤-trans
    radiusBelowFloor
    (classificationGroupUniversalCoefficientAtLeastElevenTwelfths lieType)

compactSimpleUniversalCasimirFloorLevel : ProofLevel
compactSimpleUniversalCasimirFloorLevel = machineChecked

compactSimpleUniversalBetaFloorLevel : ProofLevel
compactSimpleUniversalBetaFloorLevel = machineChecked

-- Remaining L1 physics: construct the literal same-carrier Wilson/FP/Haar scalar
-- and prove ONE cutoff/volume/scale-uniform regular remainder radius < 11/12.
literalUniformRegularRemainderBelowUniversalFloorLevel : ProofLevel
literalUniformRegularRemainderBelowUniversalFloorLevel = conditional
