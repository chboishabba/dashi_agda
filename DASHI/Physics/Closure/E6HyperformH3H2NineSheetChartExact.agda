module DASHI.Physics.Closure.E6HyperformH3H2NineSheetChartExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Physics.Closure.E6HyperformH3H2PhaseIncidenceExact as Incidence

------------------------------------------------------------------------
-- NINE-SHEET COORDINATE CHART FOR THE H3-H2 ORDER-PARAMETER FIBRE
--
-- For a selected H3 radical r, every radical-resolving projective covector
-- line has a unique representative normalised by ell(r)=1. In the selected
-- local coordinates r=(1,0,-1), those representatives are
--
--   ell_(b,c) = (1+c, b, c),   (b,c) in F3^2.
--
-- Hence the nine incident H2 faces / phase lines form an affine F3^2 torsor.
-- The repository already owns `NineSheet = KernelTrit x KernelTrit`; this owner
-- supplies an explicit finite carrier chart between that object and the two
-- affine phase coordinates. It does NOT identify pants/IIT/nonary semantics
-- with the H3-H2 incidence geometry.
------------------------------------------------------------------------

data F3Coeff : Set where
  c0 c1 c2 : F3Coeff

tritToCoeff : Triadic.KernelTrit → F3Coeff
tritToCoeff Triadic.zeroTrit = c0
tritToCoeff Triadic.positiveTrit = c1
tritToCoeff Triadic.negativeTrit = c2

coeffToTrit : F3Coeff → Triadic.KernelTrit
coeffToTrit c0 = Triadic.zeroTrit
coeffToTrit c1 = Triadic.positiveTrit
coeffToTrit c2 = Triadic.negativeTrit

coeffTritRoundTrip : (x : F3Coeff) → tritToCoeff (coeffToTrit x) ≡ x
coeffTritRoundTrip c0 = refl
coeffTritRoundTrip c1 = refl
coeffTritRoundTrip c2 = refl

tritCoeffRoundTrip : (x : Triadic.KernelTrit) → coeffToTrit (tritToCoeff x) ≡ x
tritCoeffRoundTrip Triadic.negativeTrit = refl
tritCoeffRoundTrip Triadic.zeroTrit = refl
tritCoeffRoundTrip Triadic.positiveTrit = refl

PhaseAffineCoordinate : Set
PhaseAffineCoordinate = F3Coeff × F3Coeff

nineSheetToPhaseCoordinate : Triadic.NineSheet → PhaseAffineCoordinate
nineSheetToPhaseCoordinate (x , y) = tritToCoeff x , tritToCoeff y

phaseCoordinateToNineSheet : PhaseAffineCoordinate → Triadic.NineSheet
phaseCoordinateToNineSheet (b , c) = coeffToTrit b , coeffToTrit c

nineSheetPhaseRoundTrip :
  (s : Triadic.NineSheet) →
  phaseCoordinateToNineSheet (nineSheetToPhaseCoordinate s) ≡ s
nineSheetPhaseRoundTrip (Triadic.negativeTrit , Triadic.negativeTrit) = refl
nineSheetPhaseRoundTrip (Triadic.negativeTrit , Triadic.zeroTrit) = refl
nineSheetPhaseRoundTrip (Triadic.negativeTrit , Triadic.positiveTrit) = refl
nineSheetPhaseRoundTrip (Triadic.zeroTrit , Triadic.negativeTrit) = refl
nineSheetPhaseRoundTrip (Triadic.zeroTrit , Triadic.zeroTrit) = refl
nineSheetPhaseRoundTrip (Triadic.zeroTrit , Triadic.positiveTrit) = refl
nineSheetPhaseRoundTrip (Triadic.positiveTrit , Triadic.negativeTrit) = refl
nineSheetPhaseRoundTrip (Triadic.positiveTrit , Triadic.zeroTrit) = refl
nineSheetPhaseRoundTrip (Triadic.positiveTrit , Triadic.positiveTrit) = refl

phaseNineSheetRoundTrip :
  (p : PhaseAffineCoordinate) →
  nineSheetToPhaseCoordinate (phaseCoordinateToNineSheet p) ≡ p
phaseNineSheetRoundTrip (c0 , c0) = refl
phaseNineSheetRoundTrip (c0 , c1) = refl
phaseNineSheetRoundTrip (c0 , c2) = refl
phaseNineSheetRoundTrip (c1 , c0) = refl
phaseNineSheetRoundTrip (c1 , c1) = refl
phaseNineSheetRoundTrip (c1 , c2) = refl
phaseNineSheetRoundTrip (c2 , c0) = refl
phaseNineSheetRoundTrip (c2 , c1) = refl
phaseNineSheetRoundTrip (c2 , c2) = refl

normalisedCovectorFormula : String
normalisedCovectorFormula = "ell_(b,c)=(1+c,b,c) with ell(r)=1 over F3"

record H3H2NineSheetBoundary : Set where
  constructor h3-h2-nine-sheet-boundary
  field
    nineIncidentH2FacesAlreadyPaid : Bool
    ninePhaseLinesAlreadyPaid : Bool
    phaseLineToH2KernelSameObjectPaid : Bool
    affineF3SquaredCoordinateAvailable : Bool
    existingNineSheetCarrierChartPaid : Bool
    nineSheetPantsSemanticsEqualsH2IncidenceByDefinition : Bool
    IITIntegrationSemanticsEqualsH2IncidenceByDefinition : Bool
    nonaryRingSemanticsEqualsH2IncidenceByDefinition : Bool
    boundary : String
open H3H2NineSheetBoundary public

canonicalH3H2NineSheetBoundary : H3H2NineSheetBoundary
canonicalH3H2NineSheetBoundary =
  h3-h2-nine-sheet-boundary
    true true true true true
    false false false
    "The nine H2 choices over one H3 admit an exact affine F3^2/NineSheet coordinate chart after normalising the annihilator by ell(r)=1. This is a carrier chart only. Existing pants, IIT and nonary-ring interpretations of NineSheet remain semantically independent unless separate same-action/consumer receipts are supplied."

incidenceReceipt : Incidence.H3H2PhaseIncidenceLocalReceipt
incidenceReceipt = Incidence.canonicalH3H2PhaseIncidenceLocalReceipt

data NineSheetChartCreatesIITIdentity : Set where

nineSheetChartDoesNotCreateIITIdentity :
  NineSheetChartCreatesIITIdentity → {A : Set} → A
nineSheetChartDoesNotCreateIITIdentity ()
