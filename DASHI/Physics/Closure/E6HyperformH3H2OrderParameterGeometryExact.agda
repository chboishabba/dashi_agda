module DASHI.Physics.Closure.E6HyperformH3H2OrderParameterGeometryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2PhaseIncidenceExact as Incidence
import DASHI.Physics.Closure.E6HyperformH3H2NineSheetChartExact as Nine

------------------------------------------------------------------------
-- AFFINE-ORTHOGONAL GEOMETRY OF THE NINE H2 ORDER-PARAMETER STATES
--
-- Normalise each radical-resolving covector by ell(r)=1.  The nine choices are
-- then coordinatised by (b,c) in F3^2 through
--
--   ell_(b,c) = (1+c,b,c).
--
-- The actual selected-H3 Weyl stabilizer has order 432.  Its action on these
-- nine H2/phase choices factors through a 72-element permutation group.  The
-- exact producer recovers every induced transformation as
--
--   u |-> A u + a,
--
-- where all nine translations occur and the eight distinct linear parts are
-- exactly O(2,3): A^T A = I. Hence the effective order-parameter action is
--
--   F3^2 semidirect O(2,3),  order 9*8 = 72.
--
-- This supplies a canonical invariant displacement
--
--   d2(u,v) = (u-v)^T (u-v) in F3.
--
-- Its norm-1 shell contains the four axial neighbors (+/-1,0),(0,+/-1), i.e.
-- the standard C3 x C3 torus adjacency on the existing NineSheet carrier;
-- its norm-2 shell contains the four diagonals. Thus a symmetry-derived finite
-- kinetic geometry exists before any physical kinetic coefficient is chosen.
------------------------------------------------------------------------

selectedH3StabilizerOrder : Nat
selectedH3StabilizerOrder = 432

effectiveOrderParameterActionOrder : Nat
effectiveOrderParameterActionOrder = 72

translationSubgroupOrder : Nat
translationSubgroupOrder = 9

orthogonalLinearPartOrder : Nat
orthogonalLinearPartOrder = 8

normOneNeighborCount : Nat
normOneNeighborCount = 4

normTwoShellCount : Nat
normTwoShellCount = 4

orderParameterActionDescription : String
orderParameterActionDescription = "F3^2 semidirect O(2,3), order 72"

invariantDisplacement : String
invariantDisplacement = "d2(u,v)=(u-v)^T(u-v) mod 3"

record H3H2OrderParameterGeometryLocalReceipt : Set where
  constructor h3-h2-order-parameter-geometry-local-receipt
  field
    sameNineIncidentH2CarrierUsed : Bool
    affineF3SquaredCoordinatesUsed : Bool
    fullSelectedH3StabilizerOrder432Checked : Bool
    effectiveNinePointActionOrder72Checked : Bool
    allNineTranslationsPresent : Bool
    exactlyEightLinearPartsPresent : Bool
    everyLinearPartOrthogonal : Bool
    linearPartsExhaustO23 : Bool
    semidirectProductRecognitionPaidLocally : Bool
    invariantQuadraticDisplacementPaid : Bool
    normOneShellHasFourAxialNeighbors : Bool
    normTwoShellHasFourDiagonalNeighbors : Bool
    normOneAdjacencyMatchesC3SquaredTorus : Bool
    physicalKineticCoefficientDerived : Bool
    continuumFieldActionDerived : Bool
    empiricalOrderParameterDynamicsPaid : Bool
    boundary : String
open H3H2OrderParameterGeometryLocalReceipt public

canonicalH3H2OrderParameterGeometryLocalReceipt : H3H2OrderParameterGeometryLocalReceipt
canonicalH3H2OrderParameterGeometryLocalReceipt =
  h3-h2-order-parameter-geometry-local-receipt
    true true true true true true true true true true true true true
    false false false
    "The nine H2 choices over a selected H3 form an affine F3^2 order-parameter space whose exact effective stabilizer action is F3^2 semidirect O(2,3). This canonically supplies the four-neighbor C3xC3 displacement geometry and a symmetry-invariant finite kinetic-distance carrier. No physical coefficient, continuum action, propagation law or empirical dynamics is inferred from the finite symmetry alone."

incidenceReceipt : Incidence.H3H2PhaseIncidenceLocalReceipt
incidenceReceipt = Incidence.canonicalH3H2PhaseIncidenceLocalReceipt

nineSheetBoundary : Nine.H3H2NineSheetBoundary
nineSheetBoundary = Nine.canonicalH3H2NineSheetBoundary

record H3H2OrderParameterFieldAction : Set₁ where
  field
    SpacetimeSite : Set
    OrderParameter : Set
    field : SpacetimeSite → OrderParameter
    invariantFiniteDisplacementReceipt : Set
    physicalKineticCoefficientReceipt : Set
    potentialOrSelectionLawReceipt : Set
    continuumScalingReceipt : Set
    stressEnergyVariationReceipt : Set
    empiricalCalibrationReceipt : Set
open H3H2OrderParameterFieldAction public

data FiniteOrderParameterGeometryCreatesFieldDynamics : Set where

finiteGeometryDoesNotCreateFieldDynamics :
  FiniteOrderParameterGeometryCreatesFieldDynamics → {A : Set} → A
finiteGeometryDoesNotCreateFieldDynamics ()
