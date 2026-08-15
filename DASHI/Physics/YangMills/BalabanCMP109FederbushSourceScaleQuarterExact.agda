module DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleQuarterExact where

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
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Replace the overly tiny rho/96 calibration as the critical G1 conditioning
-- target by a budget at CMP98's ACTUAL source principal-log radius |Y|<=1/12.
--
-- The standard inverse-dexp envelope used elsewhere in the repository gives
--
--   l = t/2 + t^2/6,       t=1/12,
--
-- for the principal-log Jacobian defect.  If the physical centre transport on
-- that same source chart satisfies the deliberately coarse l1 column bound
--
--   col(T-I) <= 1/6,
--
-- then T=I+(T-I) gives col(T)<=7/6, and the exact telescope gives
--
--   col(JT-I) <= l*(7/6) + 1/6 < 1/4.
--
-- Thus the normalized Federbush inverse needs NO rho/96 absolute chord
-- assumption.  The remaining source-scale analytic leaf is the concrete
-- transport-defect bound <=1/6 (and identification of the inverse-dexp envelope
-- with the literal principal-log derivative in the chosen l1 coordinates).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Mass
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportResidualControlsNormExact as TransportNorm
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Quarter
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sourceYRadius : ℚ
sourceYRadius = + 1 / 12

sourceLogDefectBound : ℚ
sourceLogDefectBound =
  (+ 1 / 2) * sourceYRadius
  + (+ 1 / 6) * sourceYRadius * sourceYRadius

sourceTransportDefectBound : ℚ
sourceTransportDefectBound = + 1 / 6

sourceTransportNormBound : ℚ
sourceTransportNormBound = 1ℚ + sourceTransportDefectBound

sourceTransportNormIsSevenSixths :
  sourceTransportNormBound ≡ + 7 / 6
sourceTransportNormIsSevenSixths = ℚRing.solve []

sourceLocalResidualBound : ℚ
sourceLocalResidualBound =
  sourceLogDefectBound * sourceTransportNormBound
    + sourceTransportDefectBound

sourceLocalResidualFitsQuarter :
  sourceLocalResidualBound ≤ Quarter.oneQuarter
sourceLocalResidualFitsQuarter =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Quarter.oneQuarter - sourceLocalResidualBound))

sourceTransportDefectGivesNorm :
  ∀ transport column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ sourceTransportDefectBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 transport column
    ≤ sourceTransportNormBound
sourceTransportDefectGivesNorm transport column defect =
  TransportNorm.transportColumnMassBelowIdentityPlusResidual
    transport column sourceTransportDefectBound defect

sourceScaleComponentResidualQuarter :
  ∀ jacobian transport column →
  (∀ selected →
    RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.logJacobianResidual jacobian) selected
    ≤ sourceLogDefectBound) →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.transportResidual transport) column
    ≤ sourceTransportDefectBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
      (Component.componentResidual jacobian transport) column
    ≤ Quarter.oneQuarter
sourceScaleComponentResidualQuarter jacobian transport column logColumns transportDefect =
  let
    local = Mass.componentResidualColumnMassBound
      jacobian transport
      sourceLogDefectBound sourceTransportNormBound
      sourceTransportDefectBound column
      (ℚP.nonNegative⁻¹ sourceLogDefectBound)
      logColumns
      (sourceTransportDefectGivesNorm transport column transportDefect)
      transportDefect
  in
  ℚP.≤-trans local sourceLocalResidualFitsQuarter

cmp109FederbushSourceScaleQuarterArithmeticLevel : ProofLevel
cmp109FederbushSourceScaleQuarterArithmeticLevel = machineChecked

cmp109FederbushSourceScaleResidualTelescopeLevel : ProofLevel
cmp109FederbushSourceScaleResidualTelescopeLevel = machineChecked

-- Genuine source-scale leaves.  Unlike the optional rho/96 calibration, these
-- are to be proved on the full CMP98/CMP109 selected Y chart:
--
--   col(J_Y-I) <= t/2+t^2/6,   t<=1/12,
--   col(Ad_{exp Y}-I) <= 1/6.
--
-- The first is aligned with the repository's inverse-dexp coefficient calculus;
-- the second should be proved from the explicit SU(2) adjoint-rotation formulas.
cmp109SourceScalePrincipalLogDefectLevel : ProofLevel
cmp109SourceScalePrincipalLogDefectLevel = conditional

cmp109SourceScaleAdjointTransportDefectLevel : ProofLevel
cmp109SourceScaleAdjointTransportDefectLevel = conditional
