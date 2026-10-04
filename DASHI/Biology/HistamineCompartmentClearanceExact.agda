module DASHI.Biology.HistamineCompartmentClearanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- HISTAMINE COMPARTMENT / CLEARANCE SEPARATION
------------------------------------------------------------------------

data HistamineCompartment : Set where
  intracellularCompartment : HistamineCompartment
  extracellularCompartment : HistamineCompartment
  centralNervousSystemCompartment : HistamineCompartment
  intestinalEpitheliumCompartment : HistamineCompartment
  systemicBloodCompartment : HistamineCompartment

data HistamineProcess : Set where
  synthesisByHDC : HistamineProcess
  releaseOrDegranulation : HistamineProcess
  hnmtMethylation : HistamineProcess
  daoOxidation : HistamineProcess
  receptorSignalling : HistamineProcess

data HistamineEnzyme : Set where
  hdc : HistamineEnzyme
  hnmt : HistamineEnzyme
  dao : HistamineEnzyme

record CompartmentProcessEdge : Set where
  constructor compartmentProcessEdge
  field
    process : HistamineProcess
    enzyme : HistamineEnzyme
    principalCompartment : HistamineCompartment
    source : Source.AttributedSource
    reading : String

open CompartmentProcessEdge public

hnmtIntracellularEdge : CompartmentProcessEdge
hnmtIntracellularEdge =
  compartmentProcessEdge
    hnmtMethylation hnmt intracellularCompartment
    Sources.yoshikawaNakamuraYanai2019
    "HNMT metabolises histamine intracellularly and is an important histamine-metabolism route in brain."

daoExtracellularEdge : CompartmentProcessEdge
daoExtracellularEdge =
  compartmentProcessEdge
    daoOxidation dao extracellularCompartment
    Sources.szukiewicz2024
    "DAO oxidises histamine along a distinct metabolism route, especially relevant to extracellular/peripheral histamine contexts."

hnmtBrainEdge : CompartmentProcessEdge
hnmtBrainEdge =
  compartmentProcessEdge
    hnmtMethylation hnmt centralNervousSystemCompartment
    Sources.yoshikawaNakamuraYanai2019
    "HNMT is expressed in brain; Hnmt disruption in mice increases brain histamine, supporting a direct central clearance role."

canonicalHistamineCompartmentEdges : List CompartmentProcessEdge
canonicalHistamineCompartmentEdges =
  hnmtIntracellularEdge
  ∷ daoExtracellularEdge
  ∷ hnmtBrainEdge
  ∷ []

data WholeBloodHistamineEqualsHNMTFlux : Set where
data WholeBloodHistamineEqualsBrainHistamine : Set where
data HistamineConcentrationIdentifiesClearanceCause : Set where
data HNMTAndDAOAreOnePathway : Set where

wholeBloodDoesNotDefinitionallyEqualHNMTFlux :
  WholeBloodHistamineEqualsHNMTFlux → ⊥
wholeBloodDoesNotDefinitionallyEqualHNMTFlux ()

wholeBloodDoesNotDefinitionallyEqualBrainHistamine :
  WholeBloodHistamineEqualsBrainHistamine → ⊥
wholeBloodDoesNotDefinitionallyEqualBrainHistamine ()

concentrationDoesNotIdentifyClearanceCause :
  HistamineConcentrationIdentifiesClearanceCause → ⊥
concentrationDoesNotIdentifyClearanceCause ()

hnmtAndDaoRemainDistinct :
  HNMTAndDAOAreOnePathway → ⊥
hnmtAndDaoRemainDistinct ()

record HistamineBalanceCoordinates : Set where
  constructor histamineBalanceCoordinates
  field
    productionReference : String
    releaseReference : String
    hnmtClearanceReference : String
    daoClearanceReference : String
    receptorOrDistributionReference : String
    compartmentReference : String
    timingReference : String

canonicalHistamineBalanceCoordinates : HistamineBalanceCoordinates
canonicalHistamineBalanceCoordinates =
  histamineBalanceCoordinates
    "histidine decarboxylase / production input"
    "mast-cell, basophil, neuronal, microbial or other release source as applicable"
    "HNMT activity/flux in specified intracellular/tissue compartment"
    "DAO activity/flux in specified extracellular/peripheral compartment"
    "distribution and receptor/signalling context"
    "specimen/tissue compartment must be explicit"
    "sampling and dynamic window must be explicit"
