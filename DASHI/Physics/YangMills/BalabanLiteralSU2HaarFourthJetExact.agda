module DASHI.Physics.YangMills.BalabanLiteralSU2HaarFourthJetExact where

------------------------------------------------------------------------
-- LITERAL SU(2) HAAR FOUR-JET IN QUATERNION EXPONENTIAL COORDINATES
--
-- PRIMARY SOURCES
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", 2nd ed., Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10
-- (1974), 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- MATHEMATICAL CONTENT
--
-- With the quaternion convention exp(t X)=cos(t r)+sinc(t r) X, r^2=|X|^2,
-- the pullback of normalized SU(2) Haar density is sinc(t r)^2.  Its local
-- action is therefore
--
--   -log(sinc(t r)^2) = r^2 t^2 / 3 + r^4 t^4 / 90 + O(t^6),
--
-- so the literal second and fourth derivatives at zero are respectively
-- (2/3) r^2 and (4/15) r^4.  This file puts both coefficients on every
-- positive bond of the repository's arbitrary periodic L^4 carrier.  It does
-- not assume a Haar loop numerator or a quadrature value.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical

------------------------------------------------------------------------
-- One-link coefficient in the actual three-coordinate tangent field.
------------------------------------------------------------------------

haarLinkRadiusSq : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkRadiusSq field (pair axis site) =
  field Physical.coordinateX (pair site axis)
    * field Physical.coordinateX (pair site axis)
  + field Physical.coordinateY (pair site axis)
    * field Physical.coordinateY (pair site axis)
  + field Physical.coordinateZ (pair site axis)
    * field Physical.coordinateZ (pair site axis)

haarLinkQuarticTaylorCoefficient : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkQuarticTaylorCoefficient field bond =
  (+ 1 / 90) * haarLinkRadiusSq field bond * haarLinkRadiusSq field bond

haarLinkQuadraticTaylorCoefficient : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkQuadraticTaylorCoefficient field bond =
  (+ 1 / 3) * haarLinkRadiusSq field bond

-- This is d^2/dt^2 of the negative logarithm of the link Haar density at
-- t=0.  It is the literal Haar quadratic-measure vertex used by the one-loop
-- tadpole, before propagator contraction.
haarLinkSecondDerivative : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkSecondDerivative field bond =
  (+ 2 / 3) * haarLinkRadiusSq field bond

-- This is d^4/dt^4 of the negative logarithm of the link Haar density at
-- t=0, not merely the t^4 Taylor coefficient.
haarLinkFourthDerivative : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkFourthDerivative field bond =
  (+ 4 / 15) * haarLinkRadiusSq field bond * haarLinkRadiusSq field bond

haarLinkCubicDerivative : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalBondCell L → ℚ
haarLinkCubicDerivative field bond = 0ℚ

------------------------------------------------------------------------
-- The finite-volume Haar action jets on all positive periodic bonds.
------------------------------------------------------------------------

physicalHaarQuarticTaylorCoefficient : ∀ {L} →
  Physical.PhysicalSU2BondField L → ℚ
physicalHaarQuarticTaylorCoefficient {L} field =
  sumRational (Physical.physicalBondCells L)
    (haarLinkQuarticTaylorCoefficient field)

physicalHaarQuadraticTaylorCoefficient : ∀ {L} →
  Physical.PhysicalSU2BondField L → ℚ
physicalHaarQuadraticTaylorCoefficient {L} field =
  sumRational (Physical.physicalBondCells L)
    (haarLinkQuadraticTaylorCoefficient field)

physicalHaarSecondDerivative : ∀ {L} → Physical.PhysicalSU2BondField L → ℚ
physicalHaarSecondDerivative {L} field =
  sumRational (Physical.physicalBondCells L)
    (haarLinkSecondDerivative field)

physicalHaarFourthDerivative : ∀ {L} → Physical.PhysicalSU2BondField L → ℚ
physicalHaarFourthDerivative {L} field =
  sumRational (Physical.physicalBondCells L)
    (haarLinkFourthDerivative field)

physicalHaarCubicDerivative : ∀ {L} → Physical.PhysicalSU2BondField L → ℚ
physicalHaarCubicDerivative {L} field =
  sumRational (Physical.physicalBondCells L)
    (haarLinkCubicDerivative field)

-- The coefficients above are literal rational finite sums.  The only missing
-- analytic input is the common chart-radius theorem which identifies the
-- truncated expansion with the exact Haar action with a uniform remainder.
-- The one-link analytic part is now derived with its explicit 2/175 fourth-
-- order constant in `BalabanLiteralSU2HaarAnalyticRemainder.md`; the remaining
-- identification is that this exponential-coordinate chart is valid on the
-- common physical weak-coupling ball.
literalSU2HaarFourthJetLevel : ProofLevel
literalSU2HaarFourthJetLevel = conditional

literalSU2HaarFiniteVolumeVertexLevel : ProofLevel
literalSU2HaarFiniteVolumeVertexLevel = conditional
