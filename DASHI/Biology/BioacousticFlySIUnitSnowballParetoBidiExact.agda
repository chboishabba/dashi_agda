module DASHI.Biology.BioacousticFlySIUnitSnowballParetoBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Physics.Units.SI as SI
import DASHI.Biology.BioacousticFlySnowballParetoBidiExact as Base

------------------------------------------------------------------------
-- SI / METROLOGY CROSS-POLLINATION FOR THE BIOACOUSTIC-FLY SNOWBALL
--
-- Thin specialization only. Physical quantities reuse DASHI.Physics.Units.SI;
-- the existing six-dimensional snowball/Pareto owner remains authoritative for
-- identity, provenance, alignment, opportunity, risk and implementation cost.
-- This owner adds one independent coordinate: unpaid unit-semantics debt.
------------------------------------------------------------------------

bipmSISource : Attr.AttributedSource
bipmSISource = Attr.mkDOISource
  "Bureau International des Poids et Mesures (BIPM)"
  "The International System of Units (SI), 9th edition, revision 4.01"
  "SI Brochure"
  "2026"
  "10.59161/AUEZ1291"
  "https://www.bipm.org/en/publications/si-brochure"
  Attr.institutionalSource
  "primary authority for SI dimensions/units only; does not identify biological carriers, experiments or causal mechanisms"
  Attr.publicAttribution

oneUnit : SI.Unit SI.Dimensionless
oneUnit = SI.mkUnit "1" "one"

record PhysicalCoordinateReceipt : Set₁ where
  constructor physicalCoordinateReceipt
  field
    coordinateName : String
    dimension : SI.Dimension
    decimalScale : SI.DecimalScale
    unit : SI.Unit dimension
    valueReference : String
    provenanceReference : String
    physicallyInterpretable : Bool
    exactNumericValuePaid : Bool

open PhysicalCoordinateReceipt public

protocolRateReceipt : PhysicalCoordinateReceipt
protocolRateReceipt = physicalCoordinateReceipt
  "Gauthey conventional-2P aligned protocol rate"
  SI.Frequency
  SI.unitScale
  SI.hertz
  "2.20337115787 Hz"
  Base.paidTimebaseReference
  true
  true

protocolTimeReceipt : PhysicalCoordinateReceipt
protocolTimeReceipt = physicalCoordinateReceipt
  "Gauthey aligned protocol time"
  SI.Time
  SI.unitScale
  SI.second
  "668 samples on the source-code-paid aligned timebase; per-sample time is interpreted through the recorded rate"
  Base.paidTimebaseReference
  true
  true

acousticFrequencyReceipt : PhysicalCoordinateReceipt
acousticFrequencyReceipt = physicalCoordinateReceipt
  "birdsong pitch / spectral-frequency coordinate when present"
  SI.Frequency
  SI.unitScale
  SI.hertz
  "feature-specific numeric values remain source-row dependent"
  "Arese/SoundPlot acoustic feature producers"
  true
  false

microscopyLengthReceipt : PhysicalCoordinateReceipt
microscopyLengthReceipt = physicalCoordinateReceipt
  "microscopy anatomical length coordinate when a registered spatial carrier supplies one"
  SI.Length
  SI.microScale
  SI.metre
  "micrometre-scale length; exact coordinate values remain dataset/registration dependent"
  "functional/anatomical registration producer"
  true
  false

embeddingCoordinateReceipt : PhysicalCoordinateReceipt
embeddingCoordinateReceipt = physicalCoordinateReceipt
  "PCA/UMAP/rendered state-space coordinate"
  SI.Dimensionless
  SI.unitScale
  oneUnit
  "dimensionless latent/diagnostic coordinate"
  "DASHI downstream embedding/rendering producer"
  false
  false

protocolRateUnit : SI.Unit SI.Frequency
protocolRateUnit = SI.hertz

protocolTimeUnit : SI.Unit SI.Time
protocolTimeUnit = SI.second

microscopyLengthScale : SI.DecimalScale
microscopyLengthScale = SI.microScale

embeddingCoordinatesDimensionless : Bool
embeddingCoordinatesDimensionless = true

------------------------------------------------------------------------
-- Seventh independent Pareto coordinate.
------------------------------------------------------------------------

data SIExtendedFrontierAxis : Set where
  sameObjectDebt temporalAlignmentDebt provenanceDebt opportunityLoss
  identityRisk implementationCost unitSemanticsDebt : SIExtendedFrontierAxis

axisReference : SIExtendedFrontierAxis → String
axisReference sameObjectDebt = Base.axisReference Base.sameObjectDebt
axisReference temporalAlignmentDebt = Base.axisReference Base.temporalAlignmentDebt
axisReference provenanceDebt = Base.axisReference Base.provenanceDebt
axisReference opportunityLoss = Base.axisReference Base.opportunityLoss
axisReference identityRisk = Base.axisReference Base.identityRisk
axisReference implementationCost = Base.axisReference Base.implementationCost
axisReference unitSemanticsDebt =
  "unpaid physical-dimension/unit/scale semantics required by the consuming interpretation"

leafCost : SIExtendedFrontierAxis → Base.FrontierLeaf → Nat
leafCost sameObjectDebt leaf = Base.leafCost Base.sameObjectDebt leaf
leafCost temporalAlignmentDebt leaf = Base.leafCost Base.temporalAlignmentDebt leaf
leafCost provenanceDebt leaf = Base.leafCost Base.provenanceDebt leaf
leafCost opportunityLoss leaf = Base.leafCost Base.opportunityLoss leaf
leafCost identityRisk leaf = Base.leafCost Base.identityRisk leaf
leafCost implementationCost leaf = Base.leafCost Base.implementationCost leaf
leafCost unitSemanticsDebt Base.exactExternalManifest = 0
leafCost unitSemanticsDebt Base.sameTrialStimulusFunctionalTimebase = 0
leafCost unitSemanticsDebt Base.roiTrialPlaneIdentity = 0
leafCost unitSemanticsDebt Base.functionalToMaleCNSRegistration = 2
leafCost unitSemanticsDebt Base.rendererPolish = 4

extendedFrontierProblem : Pareto.ConsumerMDLProblem
extendedFrontierProblem = Pareto.consumerMDLProblem
  Base.FrontierLeaf
  (λ _ → ⊤)
  (λ _ → ⊤)
  (leafCost implementationCost)
  _≡_
  Base.leafReference
  "application-declared ordinal axes; SI semantics remain independent of identity/provenance debt"
  "highest-alpha admissible unpaid evidence/acquisition leaf with physical-unit debt retained"

extendedFrontierCosts : Pareto.CostHyperfabric extendedFrontierProblem
extendedFrontierCosts = Pareto.costHyperfabric SIExtendedFrontierAxis leafCost axisReference

extendedFrontierView : NDim.NDimParetoView extendedFrontierCosts
extendedFrontierView = NDim.ndimParetoView
  7
  "seven explicitly declared debt/risk/cost/unit axes"
  axisReference
  true
  "inspect the non-dominated frontier without scalarising physical-unit debt into identity or implementation cost"

currentInspectionFrontier : List Base.FrontierLeaf
currentInspectionFrontier = Base.currentInspectionFrontier

firstExecutionLeaf : Base.FrontierLeaf
firstExecutionLeaf = Base.firstExecutionLeaf

parallelAcquisitionLeaf : Base.FrontierLeaf
parallelAcquisitionLeaf = Base.parallelAcquisitionLeaf

------------------------------------------------------------------------
-- Bidi interpretation: physical semantics may refine a claim, but cannot pay
-- carrier identity, provenance, causal authority or anatomical registration.
------------------------------------------------------------------------

record SIUnitSnowballBoundary : Set where
  constructor siUnitSnowballBoundary
  field
    unitsDoNotCreateSameObjectIdentity : Bool
    unitsDoNotCreateCausalAuthority : Bool
    dimensionlessEmbeddingDoesNotBecomePhysicalCoordinate : Bool
    hertzDoesNotIdentifyStimulusCarrier : Bool
    secondsDoNotIdentifySameTrial : Bool
    micrometreScaleDoesNotRegisterNeuronIdentity : Bool
    unitDebtMayRemainIndependentOnParetoFrontier : Bool
    physicalInterpretationRequiresDeclaredDimensionAndUnit : Bool

open SIUnitSnowballBoundary public

canonicalSIUnitSnowballBoundary : SIUnitSnowballBoundary
canonicalSIUnitSnowballBoundary = siUnitSnowballBoundary
  true true true true true true true true

siBidiForwardReading : String
siBidiForwardReading =
  "A paid source quantity may be interpreted with its declared SI dimension/unit/scale; latent PCA/UMAP/render coordinates remain dimensionless unless a separate physical map is paid."

siBidiReverseReading : String
siBidiReverseReading =
  "If a downstream interpretation requires physical time, frequency or spatial scale and the producer lacks a unit receipt, reopen unit-semantics debt without invalidating already-paid source identity or non-physical embedding coordinates."

highestAlphaWithSIReading : String
highestAlphaWithSIReading =
  "SI cross-pollination does not reorder the current execution frontier: pooled ROI trial/plane/cluster identity remains first, exact manifest/hash closure remains parallel, and MaleCNS registration remains live but higher-risk/cost. The new seventh axis prevents future spatial/temporal interpretations from silently treating dimensionless embedding coordinates or unitless indices as physical measurements."
