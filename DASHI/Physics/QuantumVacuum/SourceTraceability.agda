module DASHI.Physics.QuantumVacuum.SourceTraceability where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- Source receipts distinguish established equations, literature proposals,
-- private communications, simulations and incomplete experiments in the DIA
-- survey.  They do not promote a physical claim by themselves.
------------------------------------------------------------------------

data SourceKind : Set where
  establishedEquation : SourceKind
  peerReviewedProposal : SourceKind
  patentProposal       : SourceKind
  numericalStudy       : SourceKind
  preliminaryExperiment : SourceKind
  privateCommunication : SourceKind
  intelligenceAssessment : SourceKind

record DocumentReceipt : Set where
  constructor mkDocumentReceipt
  field
    identifier : String
    title      : String
    publicationYear : Nat
    page       : Nat
    section    : String
    sourceKind : SourceKind

record SourceBoundConjecture : Set where
  constructor mkSourceBoundConjecture
  field
    mechanism : Surface.Mechanism
    receipt   : DocumentReceipt

DIAQuantumVacuumSurvey : Nat → String → SourceKind → DocumentReceipt
DIAQuantumVacuumSurvey page section kind =
  mkDocumentReceipt
    "DIA-08-1004-007"
    "Concepts for Extracting Energy From the Quantum Vacuum"
    2010
    page
    section
    kind

sourceReceiptDoesNotPromote : SourceBoundConjecture → Surface.ExtractionClaim
sourceReceiptDoesNotPromote c =
  Surface.surveyedMechanismClaim
    (SourceBoundConjecture.mechanism c)
    Surface.transient
    Surface.theoreticalProposal
