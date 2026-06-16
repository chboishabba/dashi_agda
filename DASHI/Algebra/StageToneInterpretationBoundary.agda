module DASHI.Algebra.StageToneInterpretationBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  )
open import LogicTlurey using
  ( Stage
  ; seed ; counter ; resonance ; overflow
  ; stageTone
  )
open import DASHI.Interop.SensibLawResidualLattice using
  ( ResidualLevel
  ; exact ; partial ; noTypedMeet ; contradiction
  )
open import DASHI.Algebra.TetralemmaBridge using
  ( TetralemmaPosition
  ; affirmation ; negation ; both ; neither
  ; stageTetralemma
  ; tetralemmaTone
  ; triResidual
  ; stageTone-via-tetralemma
  ; triResidual-excludes-contradiction
  )

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Stage tone interpretation boundary.
--
-- This module records the small formal receipt around LogicTlurey stageTone
-- and TetralemmaBridge.  It checks only the executable stage/tone/residual
-- rows and the contradiction exclusion inherited from TriTruth -> Residual.
-- It does not promote social, theological, philosophical, political, or
-- economic interpretations.

data CheckedStageToneFact : Set where
  checkedStageToneProjectsToTriTruth :
    CheckedStageToneFact
  checkedOverflowProjectsToTriLow :
    CheckedStageToneFact
  checkedTetralemmaToneFactorization :
    CheckedStageToneFact
  checkedTriTruthResidualExcludesContradiction :
    CheckedStageToneFact

data UncheckedInterpretationClaim : Set where
  socialDevelopmentStagesUnchecked :
    UncheckedInterpretationClaim
  theologyUnchecked :
    UncheckedInterpretationClaim
  lacanianReadingUnchecked :
    UncheckedInterpretationClaim
  hegelianReadingUnchecked :
    UncheckedInterpretationClaim
  politicalPredictionUnchecked :
    UncheckedInterpretationClaim
  economicPredictionUnchecked :
    UncheckedInterpretationClaim

data StageToneRowName : Set where
  seedToneRow : StageToneRowName
  counterToneRow : StageToneRowName
  resonanceToneRow : StageToneRowName
  overflowToneRow : StageToneRowName

record StageToneCanonicalRow : Set where
  constructor stageToneCanonicalRow
  field
    rowName : StageToneRowName
    stage : Stage
    tone : TriTruth
    residual : ResidualLevel
    tetralemmaPosition : TetralemmaPosition
    toneComputes :
      stageTone stage ≡ tone
    residualComputes :
      triResidual tone ≡ residual
    tetralemmaComputes :
      stageTetralemma stage ≡ tetralemmaPosition
    toneFactorsThroughTetralemma :
      stageTone stage ≡ tetralemmaTone tetralemmaPosition

seedStageToneRow : StageToneCanonicalRow
seedStageToneRow =
  stageToneCanonicalRow
    seedToneRow
    seed
    tri-low
    exact
    affirmation
    refl
    refl
    refl
    refl

counterStageToneRow : StageToneCanonicalRow
counterStageToneRow =
  stageToneCanonicalRow
    counterToneRow
    counter
    tri-mid
    partial
    negation
    refl
    refl
    refl
    refl

resonanceStageToneRow : StageToneCanonicalRow
resonanceStageToneRow =
  stageToneCanonicalRow
    resonanceToneRow
    resonance
    tri-high
    noTypedMeet
    both
    refl
    refl
    refl
    refl

overflowStageToneRow : StageToneCanonicalRow
overflowStageToneRow =
  stageToneCanonicalRow
    overflowToneRow
    overflow
    tri-low
    exact
    neither
    refl
    refl
    refl
    refl

canonicalStageToneRows : List StageToneCanonicalRow
canonicalStageToneRows =
  seedStageToneRow
  ∷ counterStageToneRow
  ∷ resonanceStageToneRow
  ∷ overflowStageToneRow
  ∷ []

overflowProjectsToTriLow :
  stageTone overflow ≡ tri-low
overflowProjectsToTriLow = refl

overflowResidualProjectsToExact :
  triResidual (stageTone overflow) ≡ exact
overflowResidualProjectsToExact = refl

stageToneResidualExcludesContradiction :
  ∀ s →
  triResidual (stageTone s) ≢ contradiction
stageToneResidualExcludesContradiction seed =
  triResidual-excludes-contradiction tri-low
stageToneResidualExcludesContradiction counter =
  triResidual-excludes-contradiction tri-mid
stageToneResidualExcludesContradiction resonance =
  triResidual-excludes-contradiction tri-high
stageToneResidualExcludesContradiction overflow =
  triResidual-excludes-contradiction tri-low

data InterpretationClaim : Set where
  stageToneVocabularyClaim :
    InterpretationClaim
  tetralemmaVocabularyClaim :
    InterpretationClaim
  residualBoundaryClaim :
    InterpretationClaim
  socialDevelopmentStageClaim :
    InterpretationClaim
  theologicalClaim :
    InterpretationClaim
  lacanianClaim :
    InterpretationClaim
  hegelianClaim :
    InterpretationClaim
  politicalPredictionClaim :
    InterpretationClaim
  economicPredictionClaim :
    InterpretationClaim

data ClaimPromotionVerdict : Set where
  checkedCarrierOnly : ClaimPromotionVerdict
  notPromoted : ClaimPromotionVerdict

record NonPromotingInterpretationClaim : Set where
  constructor nonPromotingInterpretationClaim
  field
    claim : InterpretationClaim
    verdict : ClaimPromotionVerdict
    promoted : Bool
    promotedIsFalse : promoted ≡ false
    note : String

stageToneVocabularyNonPromotingClaim : NonPromotingInterpretationClaim
stageToneVocabularyNonPromotingClaim =
  nonPromotingInterpretationClaim
    stageToneVocabularyClaim
    checkedCarrierOnly
    false
    refl
    "stageTone rows are executable carrier rows only"

tetralemmaVocabularyNonPromotingClaim : NonPromotingInterpretationClaim
tetralemmaVocabularyNonPromotingClaim =
  nonPromotingInterpretationClaim
    tetralemmaVocabularyClaim
    checkedCarrierOnly
    false
    refl
    "Tetralemma positions are vocabulary labels, not interpretive authority"

residualBoundaryNonPromotingClaim : NonPromotingInterpretationClaim
residualBoundaryNonPromotingClaim =
  nonPromotingInterpretationClaim
    residualBoundaryClaim
    checkedCarrierOnly
    false
    refl
    "TriTruth residual projection excludes contradiction but does not explain contradiction"

socialDevelopmentStageNonPromotingClaim : NonPromotingInterpretationClaim
socialDevelopmentStageNonPromotingClaim =
  nonPromotingInterpretationClaim
    socialDevelopmentStageClaim
    notPromoted
    false
    refl
    "No social development stage theory is checked here"

theologicalNonPromotingClaim : NonPromotingInterpretationClaim
theologicalNonPromotingClaim =
  nonPromotingInterpretationClaim
    theologicalClaim
    notPromoted
    false
    refl
    "No theological interpretation is checked here"

lacanianNonPromotingClaim : NonPromotingInterpretationClaim
lacanianNonPromotingClaim =
  nonPromotingInterpretationClaim
    lacanianClaim
    notPromoted
    false
    refl
    "No Lacanian interpretation is checked here"

hegelianNonPromotingClaim : NonPromotingInterpretationClaim
hegelianNonPromotingClaim =
  nonPromotingInterpretationClaim
    hegelianClaim
    notPromoted
    false
    refl
    "No Hegelian interpretation is checked here"

politicalPredictionNonPromotingClaim : NonPromotingInterpretationClaim
politicalPredictionNonPromotingClaim =
  nonPromotingInterpretationClaim
    politicalPredictionClaim
    notPromoted
    false
    refl
    "No political prediction is checked here"

economicPredictionNonPromotingClaim : NonPromotingInterpretationClaim
economicPredictionNonPromotingClaim =
  nonPromotingInterpretationClaim
    economicPredictionClaim
    notPromoted
    false
    refl
    "No economic prediction is checked here"

canonicalNonPromotingInterpretationClaims :
  List NonPromotingInterpretationClaim
canonicalNonPromotingInterpretationClaims =
  stageToneVocabularyNonPromotingClaim
  ∷ tetralemmaVocabularyNonPromotingClaim
  ∷ residualBoundaryNonPromotingClaim
  ∷ socialDevelopmentStageNonPromotingClaim
  ∷ theologicalNonPromotingClaim
  ∷ lacanianNonPromotingClaim
  ∷ hegelianNonPromotingClaim
  ∷ politicalPredictionNonPromotingClaim
  ∷ economicPredictionNonPromotingClaim
  ∷ []

socialDevelopmentStagesPromotion : Bool
socialDevelopmentStagesPromotion = false

theologyPromotion : Bool
theologyPromotion = false

lacanianHegelianReadingPromotion : Bool
lacanianHegelianReadingPromotion = false

politicalEconomicPredictionPromotion : Bool
politicalEconomicPredictionPromotion = false

socialDevelopmentStagesPromotionIsFalse :
  socialDevelopmentStagesPromotion ≡ false
socialDevelopmentStagesPromotionIsFalse = refl

theologyPromotionIsFalse :
  theologyPromotion ≡ false
theologyPromotionIsFalse = refl

lacanianHegelianReadingPromotionIsFalse :
  lacanianHegelianReadingPromotion ≡ false
lacanianHegelianReadingPromotionIsFalse = refl

politicalEconomicPredictionPromotionIsFalse :
  politicalEconomicPredictionPromotion ≡ false
politicalEconomicPredictionPromotionIsFalse = refl

record StageToneInterpretationBoundary : Set₁ where
  field
    checkedFacts :
      List CheckedStageToneFact

    uncheckedClaims :
      List UncheckedInterpretationClaim

    canonicalRows :
      List StageToneCanonicalRow

    nonPromotingClaims :
      List NonPromotingInterpretationClaim

    overflowToneCheck :
      stageTone overflow ≡ tri-low

    overflowResidualCheck :
      triResidual (stageTone overflow) ≡ exact

    stageToneFactors :
      ∀ s →
      stageTone s ≡ tetralemmaTone (stageTetralemma s)

    residualExcludesContradiction :
      ∀ t →
      triResidual t ≢ contradiction

    stageToneResidualExclusion :
      ∀ s →
      triResidual (stageTone s) ≢ contradiction

    socialDevelopmentStagesPromoted :
      Bool

    socialDevelopmentStagesPromotedIsFalse :
      socialDevelopmentStagesPromoted ≡ false

    theologyPromoted :
      Bool

    theologyPromotedIsFalse :
      theologyPromoted ≡ false

    lacanianHegelianReadingsPromoted :
      Bool

    lacanianHegelianReadingsPromotedIsFalse :
      lacanianHegelianReadingsPromoted ≡ false

    politicalEconomicPredictionsPromoted :
      Bool

    politicalEconomicPredictionsPromotedIsFalse :
      politicalEconomicPredictionsPromoted ≡ false

    receiptNotes :
      List String

canonicalStageToneInterpretationBoundary :
  StageToneInterpretationBoundary
canonicalStageToneInterpretationBoundary =
  record
    { checkedFacts =
        checkedStageToneProjectsToTriTruth
        ∷ checkedOverflowProjectsToTriLow
        ∷ checkedTetralemmaToneFactorization
        ∷ checkedTriTruthResidualExcludesContradiction
        ∷ []
    ; uncheckedClaims =
        socialDevelopmentStagesUnchecked
        ∷ theologyUnchecked
        ∷ lacanianReadingUnchecked
        ∷ hegelianReadingUnchecked
        ∷ politicalPredictionUnchecked
        ∷ economicPredictionUnchecked
        ∷ []
    ; canonicalRows =
        canonicalStageToneRows
    ; nonPromotingClaims =
        canonicalNonPromotingInterpretationClaims
    ; overflowToneCheck =
        overflowProjectsToTriLow
    ; overflowResidualCheck =
        overflowResidualProjectsToExact
    ; stageToneFactors =
        stageTone-via-tetralemma
    ; residualExcludesContradiction =
        triResidual-excludes-contradiction
    ; stageToneResidualExclusion =
        stageToneResidualExcludesContradiction
    ; socialDevelopmentStagesPromoted =
        socialDevelopmentStagesPromotion
    ; socialDevelopmentStagesPromotedIsFalse =
        socialDevelopmentStagesPromotionIsFalse
    ; theologyPromoted =
        theologyPromotion
    ; theologyPromotedIsFalse =
        theologyPromotionIsFalse
    ; lacanianHegelianReadingsPromoted =
        lacanianHegelianReadingPromotion
    ; lacanianHegelianReadingsPromotedIsFalse =
        lacanianHegelianReadingPromotionIsFalse
    ; politicalEconomicPredictionsPromoted =
        politicalEconomicPredictionPromotion
    ; politicalEconomicPredictionsPromotedIsFalse =
        politicalEconomicPredictionPromotionIsFalse
    ; receiptNotes =
        "Checked: LogicTlurey stageTone maps seed/counter/resonance/overflow to tri-low/tri-mid/tri-high/tri-low"
        ∷ "Checked: overflow projects to tri-low and exact through TriTruth -> ResidualLevel"
        ∷ "Checked: stageTone factors through TetralemmaBridge labels by definitional equality"
        ∷ "Checked: TriTruth -> ResidualLevel never returns contradiction"
        ∷ "Not checked: social development stages, theology, Lacanian or Hegelian readings"
        ∷ "Not checked: political or economic predictions"
        ∷ []
    }
