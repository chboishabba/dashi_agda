module DASHI.Foundations.CategoryPolisBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- The boundary formalised here is deliberately small:
-- scientific classification and polis membership are distinct indexed
-- judgements.  Neither is silently promoted into the other.

data Empty : Set where

¬_ : Set → Set
¬ A = A → Empty

data Frame : Set where
  scientificFrame : Frame
  moralFrame      : Frame
  legalFrame      : Frame
  politicalFrame  : Frame

data Standing : Set where
  excluded     : Standing
  held         : Standing
  included     : Standing

standingLabel : Standing → String
standingLabel excluded = "excluded"
standingLabel held     = "held"
standingLabel included = "included"

data Subject : Set where
  humanSubject           : Subject
  riverSubject           : Subject
  slimeMouldSubject      : Subject
  artificialSystemSubject : Subject
  embryoSubject          : Subject
  engineeredEmbryoSubject : Subject

subjectLabel : Subject → String
subjectLabel humanSubject            = "human"
subjectLabel riverSubject            = "river"
subjectLabel slimeMouldSubject       = "slime-mould"
subjectLabel artificialSystemSubject = "artificial-system"
subjectLabel embryoSubject           = "embryo"
subjectLabel engineeredEmbryoSubject = "engineered-embryo"

record FrameJudgement : Set where
  constructor mkFrameJudgement
  field
    frame    : Frame
    classify : Subject → Standing

open FrameJudgement public

-- A deliberately non-anthropocentric scientific probe.  It records whether
-- the subject exhibits the selected adaptive / goal-directed phenomenon; it
-- does not assign citizenship, rights, votes, or legal personality.

scientificAdaptiveStanding : Subject → Standing
scientificAdaptiveStanding humanSubject            = included
scientificAdaptiveStanding riverSubject            = held
scientificAdaptiveStanding slimeMouldSubject       = included
scientificAdaptiveStanding artificialSystemSubject = included
scientificAdaptiveStanding embryoSubject           = held
scientificAdaptiveStanding engineeredEmbryoSubject = held

scientificJudgement : FrameJudgement
scientificJudgement =
  mkFrameJudgement scientificFrame scientificAdaptiveStanding

-- Two coherent polis rules can coexist with the same scientific observations.
-- This is the constructive countermodel to any claim that scientific
-- classification alone fixes the political boundary.

humanOnlyPolis : Subject → Standing
humanOnlyPolis humanSubject = included
humanOnlyPolis _            = excluded

ecologicalPolis : Subject → Standing
ecologicalPolis humanSubject            = included
ecologicalPolis riverSubject            = included
ecologicalPolis slimeMouldSubject       = included
ecologicalPolis artificialSystemSubject = held
ecologicalPolis embryoSubject           = held
ecologicalPolis engineeredEmbryoSubject = held

humanOnlyPoliticalJudgement : FrameJudgement
humanOnlyPoliticalJudgement =
  mkFrameJudgement politicalFrame humanOnlyPolis

ecologicalPoliticalJudgement : FrameJudgement
ecologicalPoliticalJudgement =
  mkFrameJudgement politicalFrame ecologicalPolis

excluded≠included : excluded ≡ included → Empty
excluded≠included ()

scientificFrame≠politicalFrame :
  scientificFrame ≡ politicalFrame → Empty
scientificFrame≠politicalFrame ()

riverPolisDivergence :
  humanOnlyPolis riverSubject ≡ ecologicalPolis riverSubject → Empty
riverPolisDivergence = excluded≠included

slimeMouldPolisDivergence :
  humanOnlyPolis slimeMouldSubject ≡
  ecologicalPolis slimeMouldSubject →
  Empty
slimeMouldPolisDivergence = excluded≠included

-- A category error is an unlicensed transport between frames.  A bridge must
-- state both its scientific premise and the normative rule that consumes it.

record CrossoverBridge : Set where
  constructor mkCrossoverBridge
  field
    sourceFrame       : Frame
    targetFrame       : Frame
    scientificPremise : Subject → Bool
    normativeGate     : Subject → Bool
    targetStanding    : Subject → Standing
    gateSound :
      (s : Subject) →
      normativeGate s ≡ true →
      targetStanding s ≡ included

open CrossoverBridge public

unbridgedPromotion : FrameJudgement → FrameJudgement → Bool
unbridgedPromotion _ _ = false

noSilentScienceToPolis :
  unbridgedPromotion scientificJudgement
    humanOnlyPoliticalJudgement ≡ false
noSilentScienceToPolis = refl

-- Science can nevertheless affect a political or legal line through an
-- explicit crossover.  This rejects the opposite overstatement that science
-- is irrelevant to where the line is drawn.

data SafetyEvidence : Set where
  unsafeEvidence    : SafetyEvidence
  unresolvedEvidence : SafetyEvidence
  safeEvidence      : SafetyEvidence

safetyPolicy : SafetyEvidence → Standing
safetyPolicy unsafeEvidence     = excluded
safetyPolicy unresolvedEvidence = held
safetyPolicy safeEvidence       = included

safeEvidenceChangesStanding :
  safetyPolicy unsafeEvidence ≡ safetyPolicy safeEvidence → Empty
safeEvidenceChangesStanding = excluded≠included

data BiomedicalDomain : Set where
  stemCellDomain   : BiomedicalDomain
  cloningDomain    : BiomedicalDomain
  geneTherapyDomain : BiomedicalDomain
  embryoSelectionDomain : BiomedicalDomain

record BiomedicalCrossover : Set where
  constructor mkBiomedicalCrossover
  field
    domain            : BiomedicalDomain
    evidence          : SafetyEvidence
    moralAdmissible   : Bool
    resultingStanding : Standing
    evidenceApplied :
      moralAdmissible ≡ true →
      resultingStanding ≡ safetyPolicy evidence

open BiomedicalCrossover public

geneTherapySafeCrossover : BiomedicalCrossover
geneTherapySafeCrossover =
  mkBiomedicalCrossover
    geneTherapyDomain
    safeEvidence
    true
    included
    (λ _ → refl)

cloningHeldCrossover : BiomedicalCrossover
cloningHeldCrossover =
  mkBiomedicalCrossover
    cloningDomain
    unresolvedEvidence
    true
    held
    (λ _ → refl)

-- Final boundary:
--   scientific difference is neither necessary nor sufficient for polis
--   difference without a declared normative bridge;
--   scientific evidence may alter a polis decision once such a bridge exists.

record CategoryPolisBoundary : Set where
  constructor mkCategoryPolisBoundary
  field
    framesDistinct : ¬ (scientificFrame ≡ politicalFrame)
    riverUnderdeterminesPolis :
      ¬ (humanOnlyPolis riverSubject ≡ ecologicalPolis riverSubject)
    noSilentPromotion :
      unbridgedPromotion scientificJudgement
        humanOnlyPoliticalJudgement ≡ false
    scienceCanConstrainApplication :
      ¬ (safetyPolicy unsafeEvidence ≡ safetyPolicy safeEvidence)

categoryPolisBoundary : CategoryPolisBoundary
categoryPolisBoundary =
  mkCategoryPolisBoundary
    scientificFrame≠politicalFrame
    riverPolisDivergence
    noSilentScienceToPolis
    safeEvidenceChangesStanding
