module DASHI.Physics.Closure.ProjectionNonlocalityLeakagePrincipleBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.P0ClayFiniteHodgeNSTopologicalStackReceipt as P0
import DASHI.Physics.Closure.NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt as S164

------------------------------------------------------------------------
-- Projection / nonlocality leakage principle boundary.
--
-- Purpose:
--
--   Record the user's P0 insight as a fail-closed theorem target:
--
--     Projection-Nonlocality Leakage Principle
--
--   The target links the Navier-Stokes pressure leakage carried by the
--   nonlocal commutator [Pi_+, R_i R_j] with the Yang-Mills / Bruhat-Tits
--   finite Hodge-gauge leakage carried by [d_A, *].  This file records the
--   comparison surface only.  It does not prove pressure leakage, Hodge
--   gauge leakage, residual non-positivity, local defect monotonicity, a
--   no-degeneracy theorem, a finite Hodge theorem, or any promotion.

projectionNonlocalityLeakagePrincipleBoundaryLedgerClosed : Bool
projectionNonlocalityLeakagePrincipleBoundaryLedgerClosed = true

p0ClayFiniteHodgeNSTopologicalStackAnchor : Bool
p0ClayFiniteHodgeNSTopologicalStackAnchor =
  P0.sprint164BoundaryClosedAnchor
    P0.canonicalP0ClayFiniteHodgeNSTopologicalStackReceipt

nsSprint164MicrolocalTopologicalBridgeBoundaryAnchor : Bool
nsSprint164MicrolocalTopologicalBridgeBoundaryAnchor =
  S164.sprint164MicrolocalTopologicalBridgeBoundaryLedgerClosed

p0AngularCommutatorFalseAnchor : Bool
p0AngularCommutatorFalseAnchor =
  P0.AngularDegeneracyPressureCommutatorGain
    P0.canonicalP0TheoremTargetRecord

sprint164FullLocalDefectMonotonicityFalseAnchor : Bool
sprint164FullLocalDefectMonotonicityFalseAnchor =
  S164.FullLocalDefectMonotonicity

ProjectionNonlocalityLeakagePrincipleTargetRecorded : Bool
ProjectionNonlocalityLeakagePrincipleTargetRecorded = true

NSPiPlusRieszCommutatorLeakageTargetRecorded : Bool
NSPiPlusRieszCommutatorLeakageTargetRecorded = true

YMBTHodgeGaugeCommutatorLeakageTargetRecorded : Bool
YMBTHodgeGaugeCommutatorLeakageTargetRecorded = true

P0StackSourceAnchorRecorded : Bool
P0StackSourceAnchorRecorded = true

Sprint164BridgeSourceAnchorRecorded : Bool
Sprint164BridgeSourceAnchorRecorded = true

StrainEigenprojectionSymbolLemma : Bool
StrainEigenprojectionSymbolLemma = false

RieszPressureNonlocalitySymbolLemma : Bool
RieszPressureNonlocalitySymbolLemma = false

SigmaProjectionCommutatorLowerBound : Bool
SigmaProjectionCommutatorLowerBound = false

BranchSpreadImpliesPressureLeakage : Bool
BranchSpreadImpliesPressureLeakage = false

WedgeCollapseImpliesPressureStarvation : Bool
WedgeCollapseImpliesPressureStarvation = false

NoPressureCoherentDegeneracyRidingCascade : Bool
NoPressureCoherentDegeneracyRidingCascade = false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive = false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity = false

BTGaugeHodgeCompatibilityDefect : Bool
BTGaugeHodgeCompatibilityDefect = false

FiniteHodgeGaugeLeakageTerm : Bool
FiniteHodgeGaugeLeakageTerm = false

ProjectionNonlocalityLeakagePrincipleTheorem : Bool
ProjectionNonlocalityLeakagePrincipleTheorem = false

pressureLeakagePromotionAllowed : Bool
pressureLeakagePromotionAllowed = false

hodgeGaugeLeakagePromotionAllowed : Bool
hodgeGaugeLeakagePromotionAllowed = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

fullClayNSSolved : Bool
fullClayNSSolved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

yangMillsClayPromoted : Bool
yangMillsClayPromoted = false

projectionNonlocalityAnchorsP0Stack :
  p0ClayFiniteHodgeNSTopologicalStackAnchor ≡ true
projectionNonlocalityAnchorsP0Stack = refl

projectionNonlocalityAnchorsSprint164Bridge :
  nsSprint164MicrolocalTopologicalBridgeBoundaryAnchor ≡ true
projectionNonlocalityAnchorsSprint164Bridge = refl

projectionNonlocalityAnchorsP0AngularCommutatorFalse :
  p0AngularCommutatorFalseAnchor ≡ false
projectionNonlocalityAnchorsP0AngularCommutatorFalse = refl

projectionNonlocalityAnchorsSprint164FullLocalDefectFalse :
  sprint164FullLocalDefectMonotonicityFalseAnchor ≡ false
projectionNonlocalityAnchorsSprint164FullLocalDefectFalse = refl

projectionNonlocalityRecordsPrincipleTarget :
  ProjectionNonlocalityLeakagePrincipleTargetRecorded ≡ true
projectionNonlocalityRecordsPrincipleTarget = refl

projectionNonlocalityRecordsNSPressureTarget :
  NSPiPlusRieszCommutatorLeakageTargetRecorded ≡ true
projectionNonlocalityRecordsNSPressureTarget = refl

projectionNonlocalityRecordsYMBTHodgeGaugeTarget :
  YMBTHodgeGaugeCommutatorLeakageTargetRecorded ≡ true
projectionNonlocalityRecordsYMBTHodgeGaugeTarget = refl

projectionNonlocalityRecordsP0Anchor :
  P0StackSourceAnchorRecorded ≡ true
projectionNonlocalityRecordsP0Anchor = refl

projectionNonlocalityRecordsSprint164Anchor :
  Sprint164BridgeSourceAnchorRecorded ≡ true
projectionNonlocalityRecordsSprint164Anchor = refl

projectionNonlocalityKeepsStrainEigenprojectionSymbolLemmaFalse :
  StrainEigenprojectionSymbolLemma ≡ false
projectionNonlocalityKeepsStrainEigenprojectionSymbolLemmaFalse = refl

projectionNonlocalityKeepsRieszPressureNonlocalitySymbolLemmaFalse :
  RieszPressureNonlocalitySymbolLemma ≡ false
projectionNonlocalityKeepsRieszPressureNonlocalitySymbolLemmaFalse = refl

projectionNonlocalityKeepsSigmaProjectionCommutatorLowerBoundFalse :
  SigmaProjectionCommutatorLowerBound ≡ false
projectionNonlocalityKeepsSigmaProjectionCommutatorLowerBoundFalse = refl

projectionNonlocalityKeepsBranchSpreadImpliesPressureLeakageFalse :
  BranchSpreadImpliesPressureLeakage ≡ false
projectionNonlocalityKeepsBranchSpreadImpliesPressureLeakageFalse = refl

projectionNonlocalityKeepsWedgeCollapseImpliesPressureStarvationFalse :
  WedgeCollapseImpliesPressureStarvation ≡ false
projectionNonlocalityKeepsWedgeCollapseImpliesPressureStarvationFalse = refl

projectionNonlocalityKeepsNoPressureCoherentDegeneracyFalse :
  NoPressureCoherentDegeneracyRidingCascade ≡ false
projectionNonlocalityKeepsNoPressureCoherentDegeneracyFalse = refl

projectionNonlocalityKeepsNSCriticalResidualNonPositiveFalse :
  NSCriticalResidualNonPositive ≡ false
projectionNonlocalityKeepsNSCriticalResidualNonPositiveFalse = refl

projectionNonlocalityKeepsFullLocalDefectMonotonicityFalse :
  FullLocalDefectMonotonicity ≡ false
projectionNonlocalityKeepsFullLocalDefectMonotonicityFalse = refl

projectionNonlocalityKeepsBTGaugeHodgeCompatibilityDefectFalse :
  BTGaugeHodgeCompatibilityDefect ≡ false
projectionNonlocalityKeepsBTGaugeHodgeCompatibilityDefectFalse = refl

projectionNonlocalityKeepsFiniteHodgeGaugeLeakageTermFalse :
  FiniteHodgeGaugeLeakageTerm ≡ false
projectionNonlocalityKeepsFiniteHodgeGaugeLeakageTermFalse = refl

projectionNonlocalityKeepsPrincipleTheoremFalse :
  ProjectionNonlocalityLeakagePrincipleTheorem ≡ false
projectionNonlocalityKeepsPrincipleTheoremFalse = refl

projectionNonlocalityKeepsPromotionsFalse :
  pressureLeakagePromotionAllowed
  ≡
  hodgeGaugeLeakagePromotionAllowed
projectionNonlocalityKeepsPromotionsFalse = refl

data ProjectionNonlocalitySourceAnchorRow : Set where
  p0ClayFiniteHodgeNSTopologicalStack :
    ProjectionNonlocalitySourceAnchorRow
  nsSprint164MicrolocalTopologicalBridgeBoundary :
    ProjectionNonlocalitySourceAnchorRow
  p0AngularCommutatorStillFalse :
    ProjectionNonlocalitySourceAnchorRow
  sprint164FullLocalDefectMonotonicityStillFalse :
    ProjectionNonlocalitySourceAnchorRow

canonicalProjectionNonlocalitySourceAnchorRows :
  List ProjectionNonlocalitySourceAnchorRow
canonicalProjectionNonlocalitySourceAnchorRows =
  p0ClayFiniteHodgeNSTopologicalStack
  ∷ nsSprint164MicrolocalTopologicalBridgeBoundary
  ∷ p0AngularCommutatorStillFalse
  ∷ sprint164FullLocalDefectMonotonicityStillFalse
  ∷ []

projectionNonlocalitySourceAnchorRowCount : Nat
projectionNonlocalitySourceAnchorRowCount = 4

projectionNonlocalitySourceAnchorRowCountIsFour :
  projectionNonlocalitySourceAnchorRowCount ≡ 4
projectionNonlocalitySourceAnchorRowCountIsFour = refl

data ProjectionNonlocalityDataRow : Set where
  StrainEigenprojectionSymbolLemmaRow :
    ProjectionNonlocalityDataRow
  RieszPressureNonlocalitySymbolLemmaRow :
    ProjectionNonlocalityDataRow
  SigmaProjectionCommutatorLowerBoundRow :
    ProjectionNonlocalityDataRow
  BranchSpreadImpliesPressureLeakageRow :
    ProjectionNonlocalityDataRow
  WedgeCollapseImpliesPressureStarvationRow :
    ProjectionNonlocalityDataRow
  NoPressureCoherentDegeneracyRidingCascadeRow :
    ProjectionNonlocalityDataRow
  NSCriticalResidualNonPositiveRow :
    ProjectionNonlocalityDataRow
  FullLocalDefectMonotonicityRow :
    ProjectionNonlocalityDataRow
  BTGaugeHodgeCompatibilityDefectRow :
    ProjectionNonlocalityDataRow
  FiniteHodgeGaugeLeakageTermRow :
    ProjectionNonlocalityDataRow

canonicalProjectionNonlocalityDataRows :
  List ProjectionNonlocalityDataRow
canonicalProjectionNonlocalityDataRows =
  StrainEigenprojectionSymbolLemmaRow
  ∷ RieszPressureNonlocalitySymbolLemmaRow
  ∷ SigmaProjectionCommutatorLowerBoundRow
  ∷ BranchSpreadImpliesPressureLeakageRow
  ∷ WedgeCollapseImpliesPressureStarvationRow
  ∷ NoPressureCoherentDegeneracyRidingCascadeRow
  ∷ NSCriticalResidualNonPositiveRow
  ∷ FullLocalDefectMonotonicityRow
  ∷ BTGaugeHodgeCompatibilityDefectRow
  ∷ FiniteHodgeGaugeLeakageTermRow
  ∷ []

projectionNonlocalityDataRowCount : Nat
projectionNonlocalityDataRowCount = 10

projectionNonlocalityDataRowCountIsTen :
  projectionNonlocalityDataRowCount ≡ 10
projectionNonlocalityDataRowCountIsTen = refl

data ProjectionNonlocalityLeakageChannelRow : Set where
  nsPressureLeakageFromPiPlusRieszCommutator :
    ProjectionNonlocalityLeakageChannelRow
  ymBTHodgeGaugeLeakageFromDAStarCommutator :
    ProjectionNonlocalityLeakageChannelRow
  projectionNonlocalityComparisonPrinciple :
    ProjectionNonlocalityLeakageChannelRow

canonicalProjectionNonlocalityLeakageChannelRows :
  List ProjectionNonlocalityLeakageChannelRow
canonicalProjectionNonlocalityLeakageChannelRows =
  nsPressureLeakageFromPiPlusRieszCommutator
  ∷ ymBTHodgeGaugeLeakageFromDAStarCommutator
  ∷ projectionNonlocalityComparisonPrinciple
  ∷ []

projectionNonlocalityLeakageChannelRowCount : Nat
projectionNonlocalityLeakageChannelRowCount = 3

projectionNonlocalityLeakageChannelRowCountIsThree :
  projectionNonlocalityLeakageChannelRowCount ≡ 3
projectionNonlocalityLeakageChannelRowCountIsThree = refl

data ProjectionNonlocalityGapRow : Set where
  noStrainEigenprojectionSymbolLemmaProof :
    ProjectionNonlocalityGapRow
  noRieszPressureNonlocalitySymbolLemmaProof :
    ProjectionNonlocalityGapRow
  noSigmaProjectionCommutatorLowerBoundProof :
    ProjectionNonlocalityGapRow
  noBranchSpreadImpliesPressureLeakageProof :
    ProjectionNonlocalityGapRow
  noWedgeCollapseImpliesPressureStarvationProof :
    ProjectionNonlocalityGapRow
  noPressureCoherentDegeneracyRidingCascadeProof :
    ProjectionNonlocalityGapRow
  noNSCriticalResidualNonPositiveProof :
    ProjectionNonlocalityGapRow
  noFullLocalDefectMonotonicityProof :
    ProjectionNonlocalityGapRow
  noBTGaugeHodgeCompatibilityDefectProof :
    ProjectionNonlocalityGapRow
  noFiniteHodgeGaugeLeakageTermProof :
    ProjectionNonlocalityGapRow
  noProjectionNonlocalityLeakagePrincipleProof :
    ProjectionNonlocalityGapRow
  noClayPromotion :
    ProjectionNonlocalityGapRow

canonicalProjectionNonlocalityGapRows :
  List ProjectionNonlocalityGapRow
canonicalProjectionNonlocalityGapRows =
  noStrainEigenprojectionSymbolLemmaProof
  ∷ noRieszPressureNonlocalitySymbolLemmaProof
  ∷ noSigmaProjectionCommutatorLowerBoundProof
  ∷ noBranchSpreadImpliesPressureLeakageProof
  ∷ noWedgeCollapseImpliesPressureStarvationProof
  ∷ noPressureCoherentDegeneracyRidingCascadeProof
  ∷ noNSCriticalResidualNonPositiveProof
  ∷ noFullLocalDefectMonotonicityProof
  ∷ noBTGaugeHodgeCompatibilityDefectProof
  ∷ noFiniteHodgeGaugeLeakageTermProof
  ∷ noProjectionNonlocalityLeakagePrincipleProof
  ∷ noClayPromotion
  ∷ []

projectionNonlocalityGapRowCount : Nat
projectionNonlocalityGapRowCount = 12

projectionNonlocalityGapRowCountIsTwelve :
  projectionNonlocalityGapRowCount ≡ 12
projectionNonlocalityGapRowCountIsTwelve = refl

organizationString : String
organizationString =
  "O: ProjectionNonlocalityLeakagePrincipleBoundary records a P0 comparison target linking NS pressure projection nonlocality and YM/BT finite Hodge-gauge noncommutation."

requirementString : String
requirementString =
  "R: Model [Pi_+, R_iR_j] pressure leakage and [d_A,*] Hodge-gauge leakage as a shared fail-closed theorem target anchored to P0 and Sprint164."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports source anchors, the ten requested data rows, leakage-channel rows, gap rows, exact counts, false theorem flags, true target/source-anchor flags, ORCSLPGF strings, and a canonical receipt."

stateString : String
stateString =
  "S: Source anchors are recorded true; all actual theorem, proof, leakage, residual, monotonicity, gauge-defect, and promotion flags remain false."

latticeString : String
latticeString =
  "L: P0 stack + Sprint164 bridge -> NS [Pi_+, R_iR_j] leakage target and YM/BT [d_A,*] leakage target -> projection-nonlocality principle -> open proof and promotion gaps."

proposalString : String
proposalString =
  "P: Use this boundary as the shared theorem-target receipt for pressure leakage versus Hodge-gauge leakage, not as a completed analytic result."

governanceString : String
governanceString =
  "G: True appears only on target-recorded and source-anchor fields; StrainEigenprojectionSymbolLemma, RieszPressureNonlocalitySymbolLemma, SigmaProjectionCommutatorLowerBound, BranchSpreadImpliesPressureLeakage, WedgeCollapseImpliesPressureStarvation, NoPressureCoherentDegeneracyRidingCascade, NSCriticalResidualNonPositive, FullLocalDefectMonotonicity, BTGaugeHodgeCompatibilityDefect, FiniteHodgeGaugeLeakageTerm, theorem, proof, and promotion flags are false."

gapString : String
gapString =
  "F: Missing proofs are the strain eigenprojection symbol lemma, Riesz pressure nonlocality symbol lemma, Sigma commutator lower bound, pressure leakage/starvation alternatives, no coherent degeneracy cascade, NS residual sign, full local defect monotonicity, BT gauge-Hodge defect, finite Hodge leakage term, and the final leakage principle."

record ProjectionNonlocalityLeakageORCSLPGF : Set where
  constructor projectionNonlocalityLeakageORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open ProjectionNonlocalityLeakageORCSLPGF public

canonicalProjectionNonlocalityLeakageORCSLPGF :
  ProjectionNonlocalityLeakageORCSLPGF
canonicalProjectionNonlocalityLeakageORCSLPGF =
  projectionNonlocalityLeakageORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

record ProjectionNonlocalityLeakagePrincipleBoundaryReceipt : Set where
  constructor projectionNonlocalityLeakagePrincipleBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "ProjectionNonlocalityLeakagePrinciple"
    nsLeakageChannelName :
      String
    nsLeakageChannelNameIsCanonical :
      nsLeakageChannelName ≡ "NS [Pi_+, R_iR_j] pressure leakage"
    ymBTLeakageChannelName :
      String
    ymBTLeakageChannelNameIsCanonical :
      ymBTLeakageChannelName ≡ "YM/BT [d_A,*] Hodge-gauge leakage"
    orcslpgf :
      ProjectionNonlocalityLeakageORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalProjectionNonlocalityLeakageORCSLPGF
    sourceAnchors :
      List ProjectionNonlocalitySourceAnchorRow
    sourceAnchorsAreCanonical :
      sourceAnchors ≡ canonicalProjectionNonlocalitySourceAnchorRows
    dataRows :
      List ProjectionNonlocalityDataRow
    dataRowsAreCanonical :
      dataRows ≡ canonicalProjectionNonlocalityDataRows
    leakageChannels :
      List ProjectionNonlocalityLeakageChannelRow
    leakageChannelsAreCanonical :
      leakageChannels ≡ canonicalProjectionNonlocalityLeakageChannelRows
    gaps :
      List ProjectionNonlocalityGapRow
    gapsAreCanonical :
      gaps ≡ canonicalProjectionNonlocalityGapRows
    sourceAnchorRowCountField :
      projectionNonlocalitySourceAnchorRowCount ≡ 4
    dataRowCountField :
      projectionNonlocalityDataRowCount ≡ 10
    leakageChannelRowCountField :
      projectionNonlocalityLeakageChannelRowCount ≡ 3
    gapRowCountField :
      projectionNonlocalityGapRowCount ≡ 12
    principleTargetRecordedField :
      ProjectionNonlocalityLeakagePrincipleTargetRecorded ≡ true
    nsPressureTargetRecordedField :
      NSPiPlusRieszCommutatorLeakageTargetRecorded ≡ true
    ymBTHodgeGaugeTargetRecordedField :
      YMBTHodgeGaugeCommutatorLeakageTargetRecorded ≡ true
    p0SourceAnchorRecordedField :
      P0StackSourceAnchorRecorded ≡ true
    sprint164SourceAnchorRecordedField :
      Sprint164BridgeSourceAnchorRecorded ≡ true
    strainEigenprojectionSymbolLemmaFalseField :
      StrainEigenprojectionSymbolLemma ≡ false
    rieszPressureNonlocalitySymbolLemmaFalseField :
      RieszPressureNonlocalitySymbolLemma ≡ false
    sigmaProjectionCommutatorLowerBoundFalseField :
      SigmaProjectionCommutatorLowerBound ≡ false
    branchSpreadImpliesPressureLeakageFalseField :
      BranchSpreadImpliesPressureLeakage ≡ false
    wedgeCollapseImpliesPressureStarvationFalseField :
      WedgeCollapseImpliesPressureStarvation ≡ false
    noPressureCoherentDegeneracyRidingCascadeFalseField :
      NoPressureCoherentDegeneracyRidingCascade ≡ false
    nsCriticalResidualNonPositiveFalseField :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityFalseField :
      FullLocalDefectMonotonicity ≡ false
    btGaugeHodgeCompatibilityDefectFalseField :
      BTGaugeHodgeCompatibilityDefect ≡ false
    finiteHodgeGaugeLeakageTermFalseField :
      FiniteHodgeGaugeLeakageTerm ≡ false
    principleTheoremFalseField :
      ProjectionNonlocalityLeakagePrincipleTheorem ≡ false
    pressureLeakagePromotionFalseField :
      pressureLeakagePromotionAllowed ≡ false
    hodgeGaugeLeakagePromotionFalseField :
      hodgeGaugeLeakagePromotionAllowed ≡ false
    fullClayNSSolvedSnakeFalseField :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalseField :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalseField :
      clayNavierStokesPromoted ≡ false
    yangMillsClayPromotedFalseField :
      yangMillsClayPromoted ≡ false

open ProjectionNonlocalityLeakagePrincipleBoundaryReceipt public

canonicalProjectionNonlocalityLeakagePrincipleBoundaryReceipt :
  ProjectionNonlocalityLeakagePrincipleBoundaryReceipt
canonicalProjectionNonlocalityLeakagePrincipleBoundaryReceipt =
  projectionNonlocalityLeakagePrincipleBoundaryReceipt
    "ProjectionNonlocalityLeakagePrinciple"
    refl
    "NS [Pi_+, R_iR_j] pressure leakage"
    refl
    "YM/BT [d_A,*] Hodge-gauge leakage"
    refl
    canonicalProjectionNonlocalityLeakageORCSLPGF
    refl
    canonicalProjectionNonlocalitySourceAnchorRows
    refl
    canonicalProjectionNonlocalityDataRows
    refl
    canonicalProjectionNonlocalityLeakageChannelRows
    refl
    canonicalProjectionNonlocalityGapRows
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

projectionNonlocalityLeakageReceiptIsNonPromoting :
  clayNavierStokesPromoted ≡ false
projectionNonlocalityLeakageReceiptIsNonPromoting = refl

projectionNonlocalityLeakageReceiptKeepsPrincipleFalse :
  principleTheoremFalseField
    canonicalProjectionNonlocalityLeakagePrincipleBoundaryReceipt
    ≡
    refl
projectionNonlocalityLeakageReceiptKeepsPrincipleFalse = refl
