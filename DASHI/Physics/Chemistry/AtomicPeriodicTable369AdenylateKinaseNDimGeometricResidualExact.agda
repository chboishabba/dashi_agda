module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as AdK
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as FlyNDim

------------------------------------------------------------------------
-- SOURCE-PAID ADENYLATE-KINASE NDIM GEOMETRIC RESIDUAL
--
-- The previous empirical owner paid a same-sequence open/closed pair.  This
-- tranche replaces the binary conformation label by two independently retained
-- geometric coordinates from Ping et al. 2013 (DOI 10.1155/2013/628536):
--
--                         4AKE open       1AKE closed
--   NMP--CORE distance      62.7 A           18.4 A
--   LID--CORE distance      70.1 A           21.0 A
--
-- We store integer tenths of an Angstrom, so one unit here is 0.1 A = 10 pm.
-- This preserves the published decimal coordinates without introducing float
-- equality into the proof layer.
--
-- Cross-pollination from the Fly NDim owner is architectural only: keep local
-- axes distinct, do not infer that more axes automatically improve a consumer,
-- and require a separate global/functional validation.  Fly structure/function
-- semantics are not identified with protein geometry.
------------------------------------------------------------------------

data NMPGeometryBand : Set where
  nmpOpenBand : NMPGeometryBand
  nmpClosedBand : NMPGeometryBand

data LIDGeometryBand : Set where
  lidOpenBand : LIDGeometryBand
  lidClosedBand : LIDGeometryBand

record AdKGeometricResidual : Set where
  constructor adk-geometric-residual
  field
    nmpCoreTenthsAngstrom : Nat
    lidCoreTenthsAngstrom : Nat
    nmpBand : NMPGeometryBand
    lidBand : LIDGeometryBand
open AdKGeometricResidual public

openGeometricResidual : AdKGeometricResidual
openGeometricResidual = adk-geometric-residual 627 701 nmpOpenBand lidOpenBand

closedGeometricResidual : AdKGeometricResidual
closedGeometricResidual = adk-geometric-residual 184 210 nmpClosedBand lidClosedBand

geometricResidual : AdK.AdKResolvedState → AdKGeometricResidual
geometricResidual AdK.pdb4AKEState = openGeometricResidual
geometricResidual AdK.pdb1AKEState = closedGeometricResidual

nmpAxisSeparatesEndpoints :
  nmpBand openGeometricResidual ≡ nmpBand closedGeometricResidual → ⊥
nmpAxisSeparatesEndpoints ()

lidAxisSeparatesEndpoints :
  lidBand openGeometricResidual ≡ lidBand closedGeometricResidual → ⊥
lidAxisSeparatesEndpoints ()

------------------------------------------------------------------------
-- NDim donor surface.
------------------------------------------------------------------------

flyNDimDisciplineDonor : FlyNDim.FlyNDimStructureFunctionBoundary
flyNDimDisciplineDonor = FlyNDim.canonicalFlyNDimStructureFunctionBoundary

------------------------------------------------------------------------
-- Snowball attribution: DOI / QID / PDB / UniProt / Dewey / link / OEIS.
------------------------------------------------------------------------

record NDimGeometricSourceCoordinate : Set where
  constructor ndim-geometric-source-coordinate
  field
    label : String
    doi : String
    qid : String
    pdb : String
    uniprot : String
    dewey : String
    directLink : String
    oeis : String
    primaryStatus : String
    sourceRole : String

ping2013GeometricCoordinates : NDimGeometricSourceCoordinate
ping2013GeometricCoordinates =
  ndim-geometric-source-coordinate
    "Ping et al. 2013 adenylate-kinase conformational-transition geometry"
    "10.1155/2013/628536"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE open; 1AKE closed"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1155/2013/628536"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "peer-reviewed computational molecular-dynamics study using experimental crystal endpoints"
    "reports crystal endpoint geometric-center distances: NMP--CORE 62.7/18.4 A and LID--CORE 70.1/21.0 A for open/closed"

muller1996EndpointIdentity : NDimGeometricSourceCoordinate
muller1996EndpointIdentity =
  ndim-geometric-source-coordinate
    "Muller et al. 1996 open adenylate-kinase endpoint and same-chain comparison"
    "10.1016/S0969-2126(96)00018-4"
    "source-article QID unresolved; adenylate kinase Q356240"
    "4AKE compared with 1AKE"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1016/S0969-2126(96)00018-4"
    "not an integer-sequence object"
    "primary structural research article"
    "pays same-polypeptide-chain open/closed endpoint identity; does not pay the later MD mechanism"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKNDimGeometricBoundary : Set where
  constructor adk-ndim-geometric-boundary
  field
    sameSequenceEndpointPairInherited : Bool
    sameSequenceEndpointPairInheritedIsTrue :
      sameSequenceEndpointPairInherited ≡ true

    nmpCoreCoordinateSourcePaid : Bool
    nmpCoreCoordinateSourcePaidIsTrue : nmpCoreCoordinateSourcePaid ≡ true

    lidCoreCoordinateSourcePaid : Bool
    lidCoreCoordinateSourcePaidIsTrue : lidCoreCoordinateSourcePaid ≡ true

    bothMeasuredAxesSeparateEndpoints : Bool
    bothMeasuredAxesSeparateEndpointsIsTrue :
      bothMeasuredAxesSeparateEndpoints ≡ true

    axesKeptDistinctBeforeComposition : Bool
    axesKeptDistinctBeforeCompositionIsTrue :
      axesKeptDistinctBeforeComposition ≡ true

    sequenceAloneDeterminesGeometricResidual : Bool
    sequenceAloneDeterminesGeometricResidualIsFalse :
      sequenceAloneDeterminesGeometricResidual ≡ false

    moreCoordinatesAutomaticallyImproveConsumer : Bool
    moreCoordinatesAutomaticallyImproveConsumerIsFalse :
      moreCoordinatesAutomaticallyImproveConsumer ≡ false

    twoEndpointCoordinatesProveTransitionPath : Bool
    twoEndpointCoordinatesProveTransitionPathIsFalse :
      twoEndpointCoordinatesProveTransitionPath ≡ false

    geometricCenterDistancesDetermineUniqueProteinConformation : Bool
    geometricCenterDistancesDetermineUniqueProteinConformationIsFalse :
      geometricCenterDistancesDetermineUniqueProteinConformation ≡ false

    fullSE3InvariantTheoremPaid : Bool
    fullSE3InvariantTheoremPaidIsFalse : fullSE3InvariantTheoremPaid ≡ false

    coordinatePairProvesCatalyticFunction : Bool
    coordinatePairProvesCatalyticFunctionIsFalse :
      coordinatePairProvesCatalyticFunction ≡ false

canonicalAdKNDimGeometricBoundary : AdKNDimGeometricBoundary
canonicalAdKNDimGeometricBoundary =
  adk-ndim-geometric-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
