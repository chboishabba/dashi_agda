module DASHI.Physics.YangMills.BalabanCMP98Equation38NonidentityPrincipalLogProducerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Turn the explicit equation-(38) quadratic source bound into the exact
-- Round-47 same-coordinate nonidentity principal-log producer.  The source
-- theorem remains attached to the SAME remainder in `firstOrder`; all little-o
-- packaging after that source estimate is constructive and machine checked.
--
-- This is deliberately convention-neutral: callers instantiate `firstOrder`
-- with the literal left- or right-trivialized printed map and its matching J_G.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityFirstOrderExact as Round47
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

record Equation38NonidentityProducerData
    (Lie GroupLog Coord : Set) : Set₁ where
  field
    firstOrder : Round47.NonidentityPrincipalLogFirstOrderData Lie GroupLog Coord
    inputMagnitude : Lie → ℚ
    coordinateMagnitude : Coord → ℚ
    equation38Bound : ∀ xi →
      Eq38.Equation38QuadraticRemainder
        (inputMagnitude xi)
        (coordinateMagnitude
          (Round47.coords firstOrder (Round47.remainder firstOrder xi)))

open Equation38NonidentityProducerData public

Equation38LittleO :
  ∀ {Lie GroupLog Coord} →
  Equation38NonidentityProducerData Lie GroupLog Coord →
  (Lie → Coord) → Set
Equation38LittleO data remainderFunction =
  ∀ xi epsilon →
    Eq38.sourceQuadraticConstant * inputMagnitude data xi ≤ epsilon →
    coordinateMagnitude data (remainderFunction xi)
      ≤ epsilon * inputMagnitude data xi

equation38LittleOStructure :
  ∀ {Lie GroupLog Coord}
    (data : Equation38NonidentityProducerData Lie GroupLog Coord) →
  Round47.CoordinateLittleOAtZero Lie Coord ℚ
equation38LittleOStructure data = record
  { Round47.CoordinateLittleOAtZero.inputMagnitude = inputMagnitude data
  ; Round47.CoordinateLittleOAtZero.outputMagnitude = coordinateMagnitude data
  ; Round47.CoordinateLittleOAtZero.LittleO = Equation38LittleO data }

equation38SameRemainderLittleO :
  ∀ {Lie GroupLog Coord}
    (data : Equation38NonidentityProducerData Lie GroupLog Coord) →
  Equation38LittleO data
    (λ xi → Round47.coords (firstOrder data)
      (Round47.remainder (firstOrder data) xi))
equation38SameRemainderLittleO data xi epsilon small =
  Eq38.equation38RemainderLittleOEpsilon
    (inputMagnitude data xi)
    (coordinateMagnitude data
      (Round47.coords (firstOrder data)
        (Round47.remainder (firstOrder data) xi)))
    epsilon
    (equation38Bound data xi)
    small

equation38NonidentityPrincipalLogProducer :
  ∀ {Lie GroupLog Coord}
    (data : Equation38NonidentityProducerData Lie GroupLog Coord) →
  Round47.NonidentityPrincipalLogCoordinateProducer Lie GroupLog Coord ℚ
equation38NonidentityPrincipalLogProducer data = record
  { Round47.NonidentityPrincipalLogCoordinateProducer.firstOrder = firstOrder data
  ; Round47.NonidentityPrincipalLogCoordinateProducer.asymptotics =
      equation38LittleOStructure data
  ; Round47.NonidentityPrincipalLogCoordinateProducer.coordinateRemainderLittleO =
      equation38SameRemainderLittleO data }

cmp98Equation38NonidentityProducerAssemblyLevel : ProofLevel
cmp98Equation38NonidentityProducerAssemblyLevel = machineChecked

-- The source equation-(38) bound itself must still be instantiated for the
-- actual selected CMP109 points/trivializations.  This flag prevents the
-- packaging theorem above from being mistaken for that physical instantiation.
cmp98Equation38SelectedPointInstantiationLevel : ProofLevel
cmp98Equation38SelectedPointInstantiationLevel = conditional
