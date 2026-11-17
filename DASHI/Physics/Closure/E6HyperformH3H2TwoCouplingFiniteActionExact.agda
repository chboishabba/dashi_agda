module DASHI.Physics.Closure.E6HyperformH3H2TwoCouplingFiniteActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2InvariantQuadraticDynamicsExact as Fibre
import DASHI.Physics.Closure.E6HyperformH3H2IncidenceGroundStateExact as Incidence
import DASHI.Physics.Closure.E6HyperformH3H2GapNonIdentificationExact as NoGo
import DASHI.Physics.Closure.E6HyperformH3H2InvariantPotentialNoGoExact as Onsite

------------------------------------------------------------------------
-- MINIMAL TWO-COUPLING FINITE SECTION THEORY
--
-- Two separately owned symmetry structures survive the max-cut:
--
--   (1) local fibre motion on F3^2, whose nearest-shell quadratic kinetic
--       operator is unique up to scale kappa;
--
--   (2) inter-H3 incidence agreement, whose exact-cover vacua maximise the
--       already-owned H3-H2 relational interaction and whose coefficient is a
--       separate scale lambda.
--
-- The equal numerical gap 3 does not identify these operators.  Therefore the
-- most economical finite section action consistent with current theorems has
-- two independent coefficients:
--
--   S_fin = kappa * K_fibre + lambda * (180 - A_incidence).
--
-- A fully symmetric nonconstant onsite term is excluded by the translation
-- no-go.  Additional coupled-field/history/boundary terms remain admissible but
-- are not forced by the present finite geometry.
------------------------------------------------------------------------

fibreDimensionlessGap : Nat
fibreDimensionlessGap = 3

incidenceDimensionlessGap : Nat
incidenceDimensionlessGap = 3

incidenceMaximumAgreement : Nat
incidenceMaximumAgreement = 180

canonicalFiniteSectionActionShape : String
canonicalFiniteSectionActionShape =
  "S_fin = kappa*K_fibre + lambda*(180-A_incidence), with kappa and lambda independent absent a dynamical same-operator theorem"

record H3H2TwoCouplingFiniteActionBoundary : Set where
  constructor h3-h2-two-coupling-finite-action-boundary
  field
    fibreOperatorShapeSymmetryForcedUpToScale : Bool
    incidenceInteractionUsesOnlyOwnedGeometry : Bool
    fullySymmetricNonconstantOnsitePotentialExcluded : Bool
    fibreAndIncidenceOperatorsProvedNonIdentical : Bool
    equalGapThreeUsedToIdentifyCouplings : Bool
    twoIndependentCouplingsRequiredByCurrentFormalism : Bool
    fibreCouplingDerivedPhysically : Bool
    incidenceCouplingDerivedPhysically : Bool
    relativeCouplingDerivedPhysically : Bool
    continuumScalingDerived : Bool
    lorentzianActionDerived : Bool
    empiricalCalibrationPaid : Bool
    boundary : String
open H3H2TwoCouplingFiniteActionBoundary public

canonicalBoundary : H3H2TwoCouplingFiniteActionBoundary
canonicalBoundary =
  h3-h2-two-coupling-finite-action-boundary
    true true true true false true
    false false false false false false
    "Current finite symmetry fixes the fibre kinetic shape and the incidence interaction shape but does not identify their operators or coefficients. The minimal nontrivial section model therefore carries independent kappa and lambda. Equal numerical defect/spectral gaps at 3 are explicitly non-authoritative for coefficient identification. Physical coupling values, continuum/Lorentzian scaling and calibration remain external dynamical payments."

fibreReceipt : Fibre.H3H2InvariantQuadraticDynamicsLocalReceipt
fibreReceipt = Fibre.canonicalH3H2InvariantQuadraticDynamicsLocalReceipt

incidenceReceipt : Incidence.H3H2IncidenceGroundStateLocalReceipt
incidenceReceipt = Incidence.canonicalBoundary

gapNoGo : NoGo.H3H2GapNonIdentificationBoundary
gapNoGo = NoGo.canonicalBoundary

onsiteNoGo : Onsite.H3H2InvariantPotentialBoundary
onsiteNoGo = Onsite.canonicalInvariantPotentialBoundary
