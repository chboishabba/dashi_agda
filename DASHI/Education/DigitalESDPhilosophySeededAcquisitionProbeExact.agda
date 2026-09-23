module DASHI.Education.DigitalESDPhilosophySeededAcquisitionProbeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PHILOSOPHY-SEEDED ACQUISITION PROBES
--
-- Thin consumer specialization of existing repository audit-operator patterns.
-- No heavyweight philosophy owner is imported here. Producer owner/contract
-- names are provenance coordinates only and do not import doctrines/evidence.
--
-- Existing structural donors include:
--   DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact
--   DASHI.Culture.IntersectionalPowerValueFolkModelBoundary
--   DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact
--
-- A philosophy probe may reopen/source-search a residual. It cannot answer it.
------------------------------------------------------------------------

data PhilosophyProbeFamily : Set where
  foucaultInstitutionalPowerProbe : PhilosophyProbeFamily
  marxOwnershipBenefitProbe : PhilosophyProbeFamily
  feministSubjectPositionProbe : PhilosophyProbeFamily
  intersectionalJointAxisProbe : PhilosophyProbeFamily
  wittgensteinUsePracticeProbe : PhilosophyProbeFamily
  spinozaCapacityToExitProbe : PhilosophyProbeFamily
  kantNonInstrumentalisationProbe : PhilosophyProbeFamily
  levinasExceedsRepresentationProbe : PhilosophyProbeFamily
  derridaClosureResidualProbe : PhilosophyProbeFamily
  zizekExcludedResidualProbe : PhilosophyProbeFamily

record PhilosophyAcquisitionProbe : Set where
  constructor philosophy-acquisition-probe
  field
    family : PhilosophyProbeFamily
    producerModule : String
    producerAuditReading : String
    digitalESDResidual : String
    discriminatorQuestion : String
    expectedEmpiricalSeparator : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    independentEmpiricalReceiptRequired : Bool
    independentEmpiricalReceiptRequiredIsTrue :
      independentEmpiricalReceiptRequired ≡ true
    createsEmpiricalEvidence : Bool
    createsEmpiricalEvidenceIsFalse : createsEmpiricalEvidence ≡ false
    createsAuthority : Bool
    createsAuthorityIsFalse : createsAuthority ≡ false

open PhilosophyAcquisitionProbe public

mkProbe :
  PhilosophyProbeFamily → String → String → String → String → String →
  PhilosophyAcquisitionProbe
mkProbe family producer reading residual question separator =
  philosophy-acquisition-probe
    family producer reading residual question separator
    true refl
    true refl
    false refl
    false refl

operatorAtlasProducer : String
operatorAtlasProducer = "DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact"

foucaultProbe : PhilosophyAcquisitionProbe
foucaultProbe = mkProbe
  foucaultInstitutionalPowerProbe
  operatorAtlasProducer
  "Foucault power/classification audit seeds a question about institutional production of subjects/categories and legitimacy; it does not prove oppression or surveillance harm."
  "visibility/monitoring x participant authority x institutional power"
  "Who observes/classifies whom, through which institution/platform, and what practical authority does the observed person retain over intervention, correction or refusal?"
  "participant/institution empirical observations or policy/deployment evidence that distinguishes visibility, intervention authority and contestability"

marxProbe : PhilosophyAcquisitionProbe
marxProbe = mkProbe
  marxOwnershipBenefitProbe
  operatorAtlasProducer
  "Marx/material-interest audit seeds ownership, labour, benefit and commercial-capture questions; it does not prove capitalist causation by label."
  "platform ownership/data value x labour/benefit/externality incidence"
  "Who owns the platform/data/product, who performs the labour, who captures economic/institutional benefit, and where are burdens externalised?"
  "source-bounded ownership/business-model/labour/value-flow evidence tied to the actual educational object"

feministProbe : PhilosophyAcquisitionProbe
feministProbe = mkProbe
  feministSubjectPositionProbe
  operatorAtlasProducer
  "Feminist subject-position audit seeds a question about whose standpoint or originating subject position disappears in a representation."
  "representation/who-missing x participant authority"
  "Whose experience is represented, inferred or classified without that group's situated testimony or interpretive authority?"
  "direct participant evidence or explicit sampling/representation evidence separating represented subject from institutional proxy"

intersectionalProbe : PhilosophyAcquisitionProbe
intersectionalProbe = mkProbe
  intersectionalJointAxisProbe
  operatorAtlasProducer
  "Intersectional audit seeds consumer-relevant joint-axis questions; strong marginal coverage does not establish interaction coverage."
  "joint intersection fibre absent despite strong component scores"
  "Does the source observe how two or more situated coordinates interact, rather than merely reporting each marginal category?"
  "interaction-specific subgroup, qualitative, stratified or mechanism evidence on the declared joint fibre"

wittgensteinProbe : PhilosophyAcquisitionProbe
wittgensteinProbe = mkProbe
  wittgensteinUsePracticeProbe
  operatorAtlasProducer
  "Wittgenstein use/practice audit seeds a mismatch test between stable policy/category wording and actual institutional/participant practice."
  "formal policy/consent/access label x realised use/practice"
  "What does 'consent', 'opt-out', 'access', 'engagement' or 'support' mean in actual practice for the situated participant?"
  "implementation or participant evidence demonstrating the practical consequences of the named policy/category"

spinozaProbe : PhilosophyAcquisitionProbe
spinozaProbe = mkProbe
  spinozaCapacityToExitProbe
  operatorAtlasProducer
  "Spinoza capacity-to-act audit is used only as an interpretive probe for practical capability; it does not attribute a modern digital-rights doctrine to Spinoza."
  "nominal permission/choice x practical exit/revision capacity"
  "Can the learner actually refuse, leave, correct or migrate without losing educational access, support, accessibility or disproportionate time/money?"
  "same-object evidence about consequences, alternatives, switching costs, accessibility continuity or actual exercise of exit"

kantProbe : PhilosophyAcquisitionProbe
kantProbe = mkProbe
  kantNonInstrumentalisationProbe
  operatorAtlasProducer
  "Kant non-instrumentalisation audit seeds a normative question about reducing learners to institutional/data means; it does not itself establish harm or rights violation."
  "student data production x institutional/vendor purpose x participant agency"
  "Is the learner represented only as a source of data/risk/engagement metrics, or is their own purpose, choice and authority independently present?"
  "participant-governance, consent, data-use or decision-process evidence; normative analysis remains distinct from empirical observation"

levinasProbe : PhilosophyAcquisitionProbe
levinasProbe = mkProbe
  levinasExceedsRepresentationProbe
  operatorAtlasProducer
  "Levinas-inspired audit seeds the question of what person/experience exceeds the chart; no Levinas doctrine is promoted into empirical sociology."
  "who/what is absent from model, score, category or source audit"
  "Which affected people, experiences or harms cannot be represented by the current variables/categories and therefore remain residual rather than zero?"
  "qualitative testimony, exclusion analysis, failure cases or category-mismatch evidence exposing a concrete missing coordinate"

derridaProbe : PhilosophyAcquisitionProbe
derridaProbe = mkProbe
  derridaClosureResidualProbe
  operatorAtlasProducer
  "Derrida closure-residual audit seeds a non-finality test for the audit vocabulary; it does not imply that truth or evidence is impossible."
  "apparently complete audit/category set x newly exposed residual"
  "What decision-relevant distinction survives outside the current chart even after all declared axes have been scored?"
  "constructive FactorsThrough collision or admitted source requiring a distinction not recoverable from the existing projection"

zizekProbe : PhilosophyAcquisitionProbe
zizekProbe = mkProbe
  zizekExcludedResidualProbe
  operatorAtlasProducer
  "Žižek/Lacan closure audit may seed a candidate excluded-residual/master-predicate question; actual institutional gluing and evidence remain mandatory."
  "dominant success/efficiency/innovation predicate x externalised residual"
  "Which burden, constituency or failure mode must be ignored for the system's dominant success label to appear globally sufficient?"
  "empirical incidence, exclusion or externality evidence; philosophy does not manufacture the excluded object"

canonicalDigitalESDPhilosophyProbes : List PhilosophyAcquisitionProbe
canonicalDigitalESDPhilosophyProbes =
  foucaultProbe
  ∷ marxProbe
  ∷ feministProbe
  ∷ intersectionalProbe
  ∷ wittgensteinProbe
  ∷ spinozaProbe
  ∷ kantProbe
  ∷ levinasProbe
  ∷ derridaProbe
  ∷ zizekProbe
  ∷ []

------------------------------------------------------------------------
-- No-promotion / Pareto discipline.
------------------------------------------------------------------------

data PhilosophyProbeCreatesEmpiricalEvidence : Set where
data PhilosophyProbeCreatesAuthority : Set where
data PhilosophyProbeCreatesMandatoryAuditAxis : Set where
data PhilosophyProbeAutomaticallyReopensEverySource : Set where
data PhilosophyProbeSelectsWinningExplanation : Set where

philosophyProbeDoesNotCreateEmpiricalEvidence :
  PhilosophyProbeCreatesEmpiricalEvidence → ⊥
philosophyProbeDoesNotCreateEmpiricalEvidence ()

philosophyProbeDoesNotCreateAuthority : PhilosophyProbeCreatesAuthority → ⊥
philosophyProbeDoesNotCreateAuthority ()

philosophyProbeDoesNotCreateMandatoryAuditAxis :
  PhilosophyProbeCreatesMandatoryAuditAxis → ⊥
philosophyProbeDoesNotCreateMandatoryAuditAxis ()

philosophyProbeDoesNotAutomaticallyReopenEverySource :
  PhilosophyProbeAutomaticallyReopensEverySource → ⊥
philosophyProbeDoesNotAutomaticallyReopenEverySource ()

philosophyProbeDoesNotSelectWinningExplanation :
  PhilosophyProbeSelectsWinningExplanation → ⊥
philosophyProbeDoesNotSelectWinningExplanation ()

record PhilosophySeededAcquisitionProbeBoundary : Set where
  constructor philosophy-seeded-acquisition-probe-boundary
  field
    philosophyMaySeedDiscriminator : Bool
    philosophyMaySeedDiscriminatorIsTrue : philosophyMaySeedDiscriminator ≡ true
    philosophyIsEmpiricalSeparator : Bool
    philosophyIsEmpiricalSeparatorIsFalse : philosophyIsEmpiricalSeparator ≡ false
    sourceAcquisitionStillConsumerRelative : Bool
    sourceAcquisitionStillConsumerRelativeIsTrue :
      sourceAcquisitionStillConsumerRelative ≡ true
    newAuditAxisRequiresConcreteCollision : Bool
    newAuditAxisRequiresConcreteCollisionIsTrue :
      newAuditAxisRequiresConcreteCollision ≡ true

canonicalPhilosophySeededAcquisitionProbeBoundary :
  PhilosophySeededAcquisitionProbeBoundary
canonicalPhilosophySeededAcquisitionProbeBoundary =
  philosophy-seeded-acquisition-probe-boundary
    true refl
    false refl
    true refl
    true refl
