module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact as P

alignmentRegression :
  P.AdKPartialStateCoordinateAlignmentBoundary.alphaOpenEndpointComposed
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ true
  × P.AdKPartialStateCoordinateAlignmentBoundary.zetaClosedEndpointComposed
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ true
  × P.AdKPartialStateCoordinateAlignmentBoundary.intermediateLabelsRetainQualitativeRegion
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ true
  × P.AdKPartialStateCoordinateAlignmentBoundary.xiToFigureLabelAlignmentPaid
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ false
alignmentRegression = refl , refl , refl , refl

thirdCoordinateFirewallRegression :
  P.AdKPartialStateCoordinateAlignmentBoundary.namedStateDLnAssignmentsPaid
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ false
  × P.AdKPartialStateCoordinateAlignmentBoundary.partialAlignmentEqualsTotalThreeCvLookup
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ false
  × P.AdKPartialStateCoordinateAlignmentBoundary.sourceOwnsDashiCompositionTheorem
    P.canonicalAdKPartialStateCoordinateAlignmentBoundary
  ≡ false
thirdCoordinateFirewallRegression = refl , refl , refl
