module DASHI.Physics.Foundations.CMP119SUNWilsonMatrixBareNormalizationExact where

------------------------------------------------------------------------
-- LITERAL MATRIX WILSON ACTION -> SU(2) BARE 4/g^2 COEFFICIENT.
--
-- Uses the EXISTING SUNWilsonAction.sunWilsonAction, whose plaquette
-- observable is the gauge-invariant 1-Re Tr(U_p)/N, and the actual
-- finite lattice GaugeField. This is not just the two-coordinate T4
-- action carrier, and it does not assert the CMP119 complete RG
-- effective action has this unrenormalized coefficient.
--
-- Original sources:
-- K.G. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI: 10.1103/PhysRevD.10.2445.
-- T. Balaban, Commun. Math. Phys. 119 (1988) 243-285,
-- DOI: 10.1007/BF01217741 (physical source identification OPEN).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge
open import DASHI.Physics.YangMills.SUNMatrixCarrier
import DASHI.Physics.YangMills.SUNWilsonAction as Wilson
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityWilsonPlaquetteBasisOrientationExact as Orientation

four : ℚ
four = Orientation.four

module _
  {Matrix Complex Vertex : Set}
  {theory : CertifiedSUNMatrixTheory 2 Matrix Complex}
  {Edge : Vertex → Vertex → Set}
  (wilson : Wilson.SUNWilsonActionData {Scalar = ℚ} theory Edge)
  where

  MatrixGaugeField : Set
  MatrixGaugeField = GaugeField {G = SUNMatrixElement theory} Edge

  actualPlaquetteCost : MatrixGaugeField → ℚ
  actualPlaquetteCost U = Wilson.sunWilsonAction wilson U

  standardBareSU2Action : ℚ → MatrixGaugeField → ℚ
  standardBareSU2Action inverseBareSquare U =
    (four * inverseBareSquare) * actualPlaquetteCost U

  factorFourRescaledBasis : MatrixGaugeField → ℚ
  factorFourRescaledBasis U = four * actualPlaquetteCost U

  repositoryUnitCoefficientPresentation : ℚ → MatrixGaugeField → ℚ
  repositoryUnitCoefficientPresentation inverseBareSquare U =
    inverseBareSquare * factorFourRescaledBasis U

  bareActionEqualsRescaledUnitPresentation :
    ∀ inverseBareSquare U →
    standardBareSU2Action inverseBareSquare U
    ≡ repositoryUnitCoefficientPresentation inverseBareSquare U
  bareActionEqualsRescaledUnitPresentation inverseBareSquare U =
    Ring.solve-∀ inverseBareSquare (actualPlaquetteCost U)

  -- The gauge invariance proof is on the ACTUAL matrix/loop observable.
  bareSU2ActionGaugeInvariant :
    ∀ inverseBareSquare
      (gamma : GaugeTransformation Vertex (SUNMatrixElement theory))
      (U : MatrixGaugeField) →
    standardBareSU2Action inverseBareSquare
      (gaugeAction (sunMatrixGroup theory) gamma U)
    ≡ standardBareSU2Action inverseBareSquare U
  bareSU2ActionGaugeInvariant inverseBareSquare gamma U =
    cong ((four * inverseBareSquare) *_)
      (Wilson.sunWilsonActionGaugeInvariant wilson gamma U)

  -- This establishes equality of the numerical evaluations, not an
  -- identification with CMP119 E/R/B/V sectors or quantum stress.
  bareMatrixMatchesT4PlaquetteProjection :
    ∀ inverseBareSquare U →
    standardBareSU2Action inverseBareSquare U
    ≡
    T4.plaquetteCoefficientProjector
      (Orientation.standardSU2WilsonAction inverseBareSquare)
    * actualPlaquetteCost U
  bareMatrixMatchesT4PlaquetteProjection inverseBareSquare U =
    Ring.solve-∀ inverseBareSquare (actualPlaquetteCost U)

  negativePlaquetteCost : MatrixGaugeField → ℚ
  negativePlaquetteCost U = - actualPlaquetteCost U

  negativeBareWilsonCoefficient : ℚ → ℚ
  negativeBareWilsonCoefficient u = - (four * u)

  negativeOrientedActionIsSameMatrixAction :
    ∀ inverseBareSquare U →
    standardBareSU2Action inverseBareSquare U
    ≡ negativeBareWilsonCoefficient inverseBareSquare
      * negativePlaquetteCost U
  negativeOrientedActionIsSameMatrixAction inverseBareSquare U =
    Ring.solve-∀ inverseBareSquare (actualPlaquetteCost U)
