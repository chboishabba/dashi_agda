module DASHI.Biology.LeadCalciumEndToEndReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.LeadCalciumAtomicLineageRegressionExact as Base
import DASHI.Biology.IonicMimicryGeometryExact as Mimicry
import DASHI.Biology.TargetRelativeRecognitionFibreExact as Recognition
import DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact as Bidi

record LeadCalciumEndToEndReplay : Set where
  constructor leadCalciumEndToEndReplay
  field
    atomicInputReference : String
    hydrationAndSolvationReference : String
    targetRecognitionReference : String
    coordinationGeometryReference : String
    proteinConformationReference : String
    proteinFunctionReference : String
    cellSignalReference : String
    organismOutcomeReference : String
    firstCoarseCollisionReference : String
    firstSeparatingCoordinateReference : String
    dependencyReopeningReference : String
    experimentalDiscriminatorReference : String
    atomicIdentityCollapsed : Bool
    atomicIdentityCollapsedIsFalse : atomicIdentityCollapsed ≡ false
    targetLocalSubstitutionObserved : Bool
    targetLocalSubstitutionObservedIsTrue : targetLocalSubstitutionObserved ≡ true
    targetLocalSubstitutionProvesOrganismEquivalence : Bool
    targetLocalSubstitutionProvesOrganismEquivalenceIsFalse :
      targetLocalSubstitutionProvesOrganismEquivalence ≡ false
    downstreamReopeningSelective : Bool
    downstreamReopeningSelectiveIsTrue : downstreamReopeningSelective ≡ true

open LeadCalciumEndToEndReplay public

canonicalLeadCalciumEndToEndReplay : LeadCalciumEndToEndReplay
canonicalLeadCalciumEndToEndReplay =
  leadCalciumEndToEndReplay
    "Base.calciumAtomicLineage Z=20 and Base.leadAtomicLineage Z=82"
    "retain ion-specific radius/hydration/solvation residual rather than projecting to +2 charge"
    "Recognition.canonicalPbCaRecognitionFibre"
    "Mimicry canonical Pb/Ca coordination-number and geometry receipts"
    "source-conditioned EF-hand/calmodulin/PKC conformational response coordinate"
    "target activation/substitution/inhibition remains assay-specific"
    "cellular calcium-signalling consumer must be re-audited after Pb substitution"
    "dose, distribution, tissue, clearance and organism phenotype are new downstream obligations"
    "formal +2 charge and partial donor/size recognition"
    "coordination geometry / hydration / target flexibility"
    "reopen only protein/cell/organism consumers that depended on the collapsed Ca/Pb coordinate"
    "Base.canonicalPbCaBidiCandidate via active BIDI loop"
    false refl
    true refl
    false refl
    true refl

baseRegression : Base.LeadCalciumAtomicLineageRegression
baseRegression = Base.canonicalLeadCalciumAtomicLineageRegression

mimicryBoundary : Mimicry.IonicMimicryGeometryBoundary
mimicryBoundary = Mimicry.canonicalIonicMimicryGeometryBoundary

recognitionFibre : Recognition.TargetRelativeRecognitionFibre
recognitionFibre = Recognition.canonicalPbCaRecognitionFibre
