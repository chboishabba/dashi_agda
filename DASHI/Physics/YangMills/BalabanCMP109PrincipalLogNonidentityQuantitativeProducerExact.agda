module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityQuantitativeProducerExact where

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
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the Round-47 same-coordinate principal-log authority with a
-- quantitative epsilon notion of little-o.  The only remaining analytic input
-- is the source line/mean-value remainder datum at each xi; the Lipschitz ->
-- quadratic -> epsilon conversion and construction of the exact Round-47
-- NonidentityPrincipalLogCoordinateProducer are machine checked here.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityFirstOrderExact as Round47
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogNonidentityRemainderQuadraticExact as Quadratic

record QuantitativeNonidentityPrincipalLogData
    (Lie GroupLog Coord : Set) : Set₁ where
  field
    firstOrder : Round47.NonidentityPrincipalLogFirstOrderData Lie GroupLog Coord
    inputMagnitude : Lie → ℚ
    coordinateMagnitude : Coord → ℚ
    lipschitzConstant : ℚ
    jacobianVariationMagnitude : Lie → ℚ
    meanValueData : ∀ xi →
      Quadratic.PrincipalLogMeanValueRemainderData
        (inputMagnitude xi)
        lipschitzConstant
        (jacobianVariationMagnitude xi)
        (coordinateMagnitude
          (Round47.coords firstOrder (Round47.remainder firstOrder xi)))

open QuantitativeNonidentityPrincipalLogData public

QuantitativeLittleO :
  ∀ {Lie GroupLog Coord} →
  QuantitativeNonidentityPrincipalLogData Lie GroupLog Coord →
  (Lie → Coord) → Set
QuantitativeLittleO data remainderFunction =
  ∀ xi epsilon →
    lipschitzConstant data * inputMagnitude data xi ≤ epsilon →
    coordinateMagnitude data (remainderFunction xi)
      ≤ epsilon * inputMagnitude data xi

quantitativeCoordinateLittleO :
  ∀ {Lie GroupLog Coord}
    (data : QuantitativeNonidentityPrincipalLogData Lie GroupLog Coord) →
  Round47.CoordinateLittleOAtZero Lie Coord ℚ
quantitativeCoordinateLittleO data = record
  { Round47.CoordinateLittleOAtZero.inputMagnitude = inputMagnitude data
  ; Round47.CoordinateLittleOAtZero.outputMagnitude = coordinateMagnitude data
  ; Round47.CoordinateLittleOAtZero.LittleO = QuantitativeLittleO data }

quantitativePrincipalLogRemainderLittleO :
  ∀ {Lie GroupLog Coord}
    (data : QuantitativeNonidentityPrincipalLogData Lie GroupLog Coord) →
  QuantitativeLittleO data
    (λ xi → Round47.coords (firstOrder data)
      (Round47.remainder (firstOrder data) xi))
quantitativePrincipalLogRemainderLittleO data xi epsilon small =
  Quadratic.principalLogNonidentityRemainderLittleOEpsilon
    (inputMagnitude data xi)
    (lipschitzConstant data)
    (jacobianVariationMagnitude data xi)
    (coordinateMagnitude data
      (Round47.coords (firstOrder data)
        (Round47.remainder (firstOrder data) xi)))
    epsilon
    (meanValueData data xi)
    small

quantitativeNonidentityPrincipalLogProducer :
  ∀ {Lie GroupLog Coord}
    (data : QuantitativeNonidentityPrincipalLogData Lie GroupLog Coord) →
  Round47.NonidentityPrincipalLogCoordinateProducer Lie GroupLog Coord ℚ
quantitativeNonidentityPrincipalLogProducer data = record
  { Round47.NonidentityPrincipalLogCoordinateProducer.firstOrder = firstOrder data
  ; Round47.NonidentityPrincipalLogCoordinateProducer.asymptotics =
      quantitativeCoordinateLittleO data
  ; Round47.NonidentityPrincipalLogCoordinateProducer.coordinateRemainderLittleO =
      quantitativePrincipalLogRemainderLittleO data }

cmp109PrincipalLogNonidentityQuantitativeProducerLevel : ProofLevel
cmp109PrincipalLogNonidentityQuantitativeProducerLevel = machineChecked
