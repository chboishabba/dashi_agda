module DASHI.Physics.Optics.FerrocellQuantumClaimDiscriminatorExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- Scope: exact finite angular observation toy model for an ideal radial
-- linear retarder between crossed polarisers.  No Fresnel calculation,
-- real-valued Mueller inversion, or claim about a particular video frame.
-- In the ideal model I(theta) is proportional to sin^2(2 theta);
-- sample theta at integer multiples of pi/4.  The alternating Bool below
-- is an exact representation of zero/maximal intensity at these samples,
-- not an approximation to arbitrary image brightness.
------------------------------------------------------------------------

data Sector : Set where
  s0 s1 s2 s3 s4 s5 s6 s7 : Sector

rotate45 : Sector → Sector
rotate45 s0 = s1
rotate45 s1 = s2
rotate45 s2 = s3
rotate45 s3 = s4
rotate45 s4 = s5
rotate45 s5 = s6
rotate45 s6 = s7
rotate45 s7 = s0

rotate90 : Sector → Sector
rotate90 s0 = s2
rotate90 s1 = s3
rotate90 s2 = s4
rotate90 s3 = s5
rotate90 s4 = s6
rotate90 s5 = s7
rotate90 s6 = s0
rotate90 s7 = s1

reverseDirector : Sector → Sector
reverseDirector s0 = s4
reverseDirector s1 = s5
reverseDirector s2 = s6
reverseDirector s3 = s7
reverseDirector s4 = s0
reverseDirector s5 = s1
reverseDirector s6 = s2
reverseDirector s7 = s3

intensityHigh : Sector → Bool
intensityHigh s0 = false
intensityHigh s1 = true
intensityHigh s2 = false
intensityHigh s3 = true
intensityHigh s4 = false
intensityHigh s5 = true
intensityHigh s6 = false
intensityHigh s7 = true

flip : Bool → Bool
flip false = true
flip true = false

quarterTurnInvariant : ∀ s → intensityHigh (rotate90 s) ≡ intensityHigh s
quarterTurnInvariant s0 = refl
quarterTurnInvariant s1 = refl
quarterTurnInvariant s2 = refl
quarterTurnInvariant s3 = refl
quarterTurnInvariant s4 = refl
quarterTurnInvariant s5 = refl
quarterTurnInvariant s6 = refl
quarterTurnInvariant s7 = refl

eighthTurnFlipsContrast :
  ∀ s → intensityHigh (rotate45 s) ≡ flip (intensityHigh s)
eighthTurnFlipsContrast s0 = refl
eighthTurnFlipsContrast s1 = refl
eighthTurnFlipsContrast s2 = refl
eighthTurnFlipsContrast s3 = refl
eighthTurnFlipsContrast s4 = refl
eighthTurnFlipsContrast s5 = refl
eighthTurnFlipsContrast s6 = refl
eighthTurnFlipsContrast s7 = refl

reversalInvariant :
  ∀ s → intensityHigh (reverseDirector s) ≡ intensityHigh s
reversalInvariant s0 = refl
reversalInvariant s1 = refl
reversalInvariant s2 = refl
reversalInvariant s3 = refl
reversalInvariant s4 = refl
reversalInvariant s5 = refl
reversalInvariant s6 = refl
reversalInvariant s7 = refl

s0NotS4 : ¬ (s0 ≡ s4)
s0NotS4 ()

-- A two-valued image of eight sectors is not a unique inverse field map.
-- This explicit collision is stronger than merely counting constructors.
noExactDirectorDecoder :
  (decode : Bool → Sector) →
  (∀ s → decode (intensityHigh s) ≡ s) → ⊥
noExactDirectorDecoder decode inverse =
  s0NotS4 (trans (sym (inverse s0)) (inverse s4))

------------------------------------------------------------------------
-- Controlled field-polarity experiment.  The even-only retarder is a
-- deliberately restricted CLASSICAL null.  An odd response may be classical
-- (e.g. a nonreciprocal magneto-optic contribution) or may belong to a new
-- mechanism.  Seeing an odd response does not establish a quantum cause.
------------------------------------------------------------------------

data Candidate : Set where
  evenRetarder : Candidate
  oddPermittedClassical : Candidate
  oddPermittedNewMechanism : Candidate

data Experiment : Set where
  fixedOpticsFieldReversal : Experiment

data Observation : Set where
  imageInvariant : Observation
  imageChanges : Observation

language : Physical.Language Experiment
language fixedOpticsFieldReversal = ⊤

predictions : Physical.Predictions Candidate Experiment Observation
predictions evenRetarder fixedOpticsFieldReversal imageInvariant = ⊤
predictions evenRetarder fixedOpticsFieldReversal imageChanges = ⊥
predictions oddPermittedClassical fixedOpticsFieldReversal imageInvariant = ⊤
predictions oddPermittedClassical fixedOpticsFieldReversal imageChanges = ⊤
predictions oddPermittedNewMechanism fixedOpticsFieldReversal imageInvariant = ⊤
predictions oddPermittedNewMechanism fixedOpticsFieldReversal imageChanges = ⊤

oddResponseRefutesRestrictedEvenModel :
  Physical.Discriminates predictions fixedOpticsFieldReversal
    evenRetarder oddPermittedClassical
oddResponseRefutesRestrictedEvenModel = imageChanges , inj₂ (tt , (λ ()))

oddResponseDoesNotSeparateClassicalFromNewMechanism :
  Physical.EquivalentOn language predictions
    oddPermittedClassical oddPermittedNewMechanism
oddResponseDoesNotSeparateClassicalFromNewMechanism
  fixedOpticsFieldReversal included imageInvariant = (λ x → x) , (λ x → x)
oddResponseDoesNotSeparateClassicalFromNewMechanism
  fixedOpticsFieldReversal included imageChanges = (λ x → x) , (λ x → x)

------------------------------------------------------------------------
-- Quantum terminology gate.  A photographed spatial pattern does not carry
-- operational Bell data: bipartite preparation, independent choices, joint
-- event outcomes, and detection/selection audit are extra inputs.
-- This is a requirements carrier, NOT a laboratory certificate.
------------------------------------------------------------------------

record BellProtocolRequirements : Set₁ where
  field
    independentSubsystemPreparation : Set
    independentlyChosenMeasurementSettings : Set
    correlatedPerTrialOutcomes : Set
    samplingAndCoincidenceAudit : Set
    statisticalRejectionCriterion : Set

BellEvidenceObligations : BellProtocolRequirements → Set
BellEvidenceObligations requirements =
  BellProtocolRequirements.independentSubsystemPreparation requirements ×
  BellProtocolRequirements.independentlyChosenMeasurementSettings requirements ×
  BellProtocolRequirements.correlatedPerTrialOutcomes requirements ×
  BellProtocolRequirements.samplingAndCoincidenceAudit requirements ×
  BellProtocolRequirements.statisticalRejectionCriterion requirements

bellEvidenceNeedsSettingChoices : ∀ {r} → BellEvidenceObligations r →
  BellProtocolRequirements.independentlyChosenMeasurementSettings r
bellEvidenceNeedsSettingChoices evidence = proj₁ (proj₂ evidence)

bellEvidenceNeedsJointOutcomes : ∀ {r} → BellEvidenceObligations r →
  BellProtocolRequirements.correlatedPerTrialOutcomes r
bellEvidenceNeedsJointOutcomes evidence = proj₁ (proj₂ (proj₂ evidence))

record FerrocellInterpretationBoundary : Set where
  constructor ferrocell-interpretation-boundary
  field
    visualFourfoldPatternProvesPhysicalTorus : Bool
    visualFourfoldPatternProvesPhysicalTorusIsFalse :
      visualFourfoldPatternProvesPhysicalTorus ≡ false
    microscopicQuantumMagnetismImpliesBellViolation : Bool
    microscopicQuantumMagnetismImpliesBellViolationIsFalse :
      microscopicQuantumMagnetismImpliesBellViolation ≡ false
    visualSymmetryEstablishesFiveDimensionalCoupling : Bool
    visualSymmetryEstablishesFiveDimensionalCouplingIsFalse :
      visualSymmetryEstablishesFiveDimensionalCoupling ≡ false
    newPredictionRequiresControlledExperiment : Bool
    newPredictionRequiresControlledExperimentIsTrue :
      newPredictionRequiresControlledExperiment ≡ true

canonicalFerrocellInterpretationBoundary : FerrocellInterpretationBoundary
canonicalFerrocellInterpretationBoundary =
  ferrocell-interpretation-boundary false refl false refl false refl true refl
