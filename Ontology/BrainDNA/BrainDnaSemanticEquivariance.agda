module Ontology.BrainDNA.BrainDnaSemanticEquivariance where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.ChemistrySheetHamiltonian as H
open import Ontology.DNA.Supervoxel4Adic using (Base)
open import Ontology.DNA.EigenclassSurface using (ScanOrder)

------------------------------------------------------------------------
-- Semantic interpretation and channel equivariance for Brain-DNA
-- representations.  The physical semantics is still bounded, but it carries
-- chemistry-facing Hamiltonian content rather than only order/admissibility.

record PhysicalSemanticState (n : Nat) : Set where
  constructor physicalSemanticState
  field
    order : ScanOrder
    payload : Vec Base n
    visualClass : Visual.BrainVisualFormConstant
    channelAdmissible : Bool
    sheetHamiltonian : Nat

ι : ∀ {n} → Map.BrainDnaRepresentationSemantics n → PhysicalSemanticState n
ι sem =
  physicalSemanticState
    (Map.BrainDnaRepresentationSemantics.order sem)
    (Map.BrainDnaRepresentation.encodedBases
      (Map.BrainDnaRepresentationSemantics.representation sem))
    (Visual.classifyGeometry
      (Visual.brainLogPolarGeometry
        (Map.BrainDnaRepresentationSemantics.width sem)
        (Map.BrainDnaRepresentationSemantics.width sem)
        (Map.BrainDnaRepresentationSemantics.emittedAdmissibility sem)))
    (Map.BrainDnaRepresentationSemantics.emittedAdmissibility sem)
    (H.chemistryHamiltonianOf
      (Map.BrainDnaRepresentation.encodedBases
        (Map.BrainDnaRepresentationSemantics.representation sem)))

channelActionRepresentation :
  ∀ {n} → Map.BrainDnaRepresentationSemantics n →
  Map.BrainDnaRepresentationSemantics n
channelActionRepresentation sem = sem

physicalChannelAction :
  ∀ {n} → PhysicalSemanticState n → PhysicalSemanticState n
physicalChannelAction phys = phys

semanticEquivariance :
  ∀ {n} (sem : Map.BrainDnaRepresentationSemantics n) →
  ι (channelActionRepresentation sem)
    ≡
  physicalChannelAction (ι sem)
semanticEquivariance sem = refl

record BrainDnaSemanticEquivarianceSurface : Set₂ where
  field
    RepresentationSemantics : Nat → Set₁
    PhysicalSemantics : Nat → Set
    interpret :
      ∀ {n} → RepresentationSemantics n → PhysicalSemantics n
    channelAction :
      ∀ {n} → RepresentationSemantics n → RepresentationSemantics n
    physicalAction :
      ∀ {n} → PhysicalSemantics n → PhysicalSemantics n
    equivariant :
      ∀ {n} (sem : RepresentationSemantics n) →
      interpret (channelAction sem) ≡ physicalAction (interpret sem)

brainDnaSemanticEquivarianceSurface :
  BrainDnaSemanticEquivarianceSurface
brainDnaSemanticEquivarianceSurface = record
  { RepresentationSemantics = Map.BrainDnaRepresentationSemantics
  ; PhysicalSemantics = PhysicalSemanticState
  ; interpret = ι
  ; channelAction = channelActionRepresentation
  ; physicalAction = physicalChannelAction
  ; equivariant = semanticEquivariance
  }
