module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseOneDimensionalDLnProjectionAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- SOURCE-TEXT ACQUISITION: 1-D dLN PROJECTION VERSUS MULTI-CV LANDSCAPE
--
-- Li-Liu-Ji explicitly state that a one-dimensional free-energy landscape
-- against dLN shows a double-well pattern and ligand-dependent population shift,
-- but averages over theta1/theta2 states.  The multidimensional landscape using
-- theta1, theta2 and dLN exposes more complex transition pathways.
--
-- This pays a source-bounded projection limitation, not a universal theorem that
-- every one-dimensional reaction coordinate is inadequate for every query.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleEnvelope : Attr.CalibrationAttributionEnvelope
articleEnvelope = Attr.canonicalLiLiuJiCalibrationAttributionEnvelope

record ProjectionTextObservation : Set where
  constructor projection-text-observation
  field
    label : String
    sourceLocator : String
    observation : String
    interpretation : String
open ProjectionTextObservation public

dLnDoubleWell : ProjectionTextObservation
dLnDoubleWell = projection-text-observation
  "one-dimensional dLN free-energy landscape"
  "PMC4572606 Discussion: multiwell free-energy landscape; Figure S18 insets"
  "the one-dimensional free-energy landscape against dLN indicates a double-well pattern"
  "source-text statement about the dLN projection; no individual well energy or population numeral is acquired here"

dLnLigandPopulationShift : ProjectionTextObservation
dLnLigandPopulationShift = projection-text-observation
  "ligand-dependent population shift in dLN projection"
  "PMC4572606 Discussion: multiwell free-energy landscape; Figure S18 insets"
  "the dLN one-dimensional landscape indicates shifted population upon ligand binding"
  "qualitative source-text population-shift statement; not a numeric equilibrium population ratio"

dLnProjectionAveragesThetaStates : ProjectionTextObservation
dLnProjectionAveragesThetaStates = projection-text-observation
  "dLN projection averages transverse conformational states"
  "PMC4572606 Discussion: multiwell free-energy landscape"
  "the one-dimensional dLN landscape collectively averages possible states regardless of theta1 and theta2"
  "source-paid observer limitation for this AdK analysis; it does not identify which exact hidden states collide at one dLN value"

threeCvLandscapeRicher : ProjectionTextObservation
threeCvLandscapeRicher = projection-text-observation
  "three-CV multidimensional landscape"
  "PMC4572606 Discussion: multiwell free-energy landscape"
  "simultaneously mapping theta1, theta2 and dLN yields more complex conformational transition pathways"
  "source-text motivation for retaining multiple coordinates; not a proof that three CVs uniquely reconstruct the complete atomistic state"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data DoubleWellCreatesNumericPopulationRatio : Set where
data DLnAloneDeterminesFullThreeCVState : Set where
data ThreeCVLandscapeIsCompleteAtomisticState : Set where
data SourceProjectionStatementCreatesGenericObserverTheorem : Set where

doubleWellDoesNotCreateNumericPopulationRatio :
  DoubleWellCreatesNumericPopulationRatio → ⊥
doubleWellDoesNotCreateNumericPopulationRatio ()

dLnAloneDoesNotDetermineFullThreeCvState :
  DLnAloneDeterminesFullThreeCVState → ⊥
dLnAloneDoesNotDetermineFullThreeCvState ()

threeCvLandscapeDoesNotBecomeCompleteAtomisticState :
  ThreeCVLandscapeIsCompleteAtomisticState → ⊥
threeCvLandscapeDoesNotBecomeCompleteAtomisticState ()

sourceProjectionStatementDoesNotCreateGenericObserverTheorem :
  SourceProjectionStatementCreatesGenericObserverTheorem → ⊥
sourceProjectionStatementDoesNotCreateGenericObserverTheorem ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKOneDimensionalDLnProjectionBoundary : Set where
  constructor adk-one-dimensional-dln-projection-boundary
  field
    dLnOneDimensionalDoubleWellPaid : Bool
    dLnLigandPopulationShiftPaid : Bool
    dLnProjectionAveragesThetaStatesPaid : Bool
    threeCvLandscapeRicherPaid : Bool
    dLnNumericPopulationRatioPaid : Bool
    dLnAloneDeterminesFullThreeCvState : Bool
    threeCvLandscapeEqualsCompleteAtomisticState : Bool
    articleAttributionEnvelopeRetained : Bool
    articleQidRequiredForProjectionStatement : Bool
    nextResidual : String
open AdKOneDimensionalDLnProjectionBoundary public

canonicalAdKOneDimensionalDLnProjectionBoundary : AdKOneDimensionalDLnProjectionBoundary
canonicalAdKOneDimensionalDLnProjectionBoundary = adk-one-dimensional-dln-projection-boundary
  true true true true
  false false false true false
  "use the source-paid dLN projection limitation as an empirical AdK premise for query-indexed observer work, while keeping the generic adequacy theorem DASHI-owned. Continue acquiring exact intermediate-state dLN, Figure-5 free energies, and per-edge Kramers numerics from same-object manifestations."
