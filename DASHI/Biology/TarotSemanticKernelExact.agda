module DASHI.Biology.TarotSemanticKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TarotCarrierExact as Tarot

------------------------------------------------------------------------
-- Rider--Waite--Smith semantic kernel.
--
-- The table stores bounded modern interpretive ranges, not propositions
-- about a querent or future world.  Reversal is a lens over the range rather
-- than Boolean negation of the upright sentence.
------------------------------------------------------------------------

data MeaningScale : Set where
  regimeScale localProcessScale : MeaningScale

data ReversalMode : Set where
  blocked internalised excessive deficient distorted releasing : ReversalMode

record CardMeaning : Set where
  constructor cardMeaning
  field
    centralMeaning : String
    shadowOrReversal : String
    semanticScale : MeaningScale
    semanticReceipt : String

open CardMeaning public

riderWaiteSmithSemanticReceipt : String
riderWaiteSmithSemanticReceipt =
  "Rider--Waite--Smith bounded modern semantic range; interpretation remains context-indexed."

meaning : Tarot.Card → CardMeaning
meaning (Tarot.major Tarot.theFool) =
  cardMeaning "Beginning, openness, freedom, taking a leap" "Recklessness, naivete, or fear of beginning" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theMagician) =
  cardMeaning "Agency, skill, concentration, making something happen" "Manipulation, scattered ability, or unused potential" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theHighPriestess) =
  cardMeaning "Intuition, silence, hidden knowledge, receptivity" "Disconnection from intuition, secrecy, or passivity" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theEmpress) =
  cardMeaning "Growth, fertility, nurture, embodiment, abundance" "Smothering, creative blockage, or neglect of self" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theEmperor) =
  cardMeaning "Structure, authority, boundaries, stable order" "Domination, rigidity, instability, or control" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theHierophant) =
  cardMeaning "Tradition, teaching, institution, inherited belief" "Dogma, rebellion, or unconventional learning" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theLovers) =
  cardMeaning "Relationship, attraction, values, consequential choice" "Misalignment, separation, or compromised values" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theChariot) =
  cardMeaning "Directed will, discipline, movement, victory" "Loss of direction, aggression, or opposing impulses" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.strength) =
  cardMeaning "Courage, patience, compassion, mastery of instinct" "Self-doubt, repression, or uncontrolled impulse" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theHermit) =
  cardMeaning "Solitude, introspection, guidance, searching" "Isolation, avoidance, or refusal of needed reflection" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.wheelOfFortune) =
  cardMeaning "Change of cycle, contingency, turning point" "Resistance to change, repetition, or bad timing" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.justice) =
  cardMeaning "Truth, fairness, accountability, consequences" "Bias, dishonesty, or evasion of responsibility" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theHangedMan) =
  cardMeaning "Suspension, surrender, sacrifice, altered viewpoint" "Stagnation, needless sacrifice, or refusal to release" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.death) =
  cardMeaning "Ending, irreversible transformation, clearing away" "Clinging, delayed ending, or fear of transformation" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.temperance) =
  cardMeaning "Integration, moderation, healing, right proportion" "Imbalance, excess, or incompatible elements" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theDevil) =
  cardMeaning "Bondage, appetite, compulsion, material attachment" "Recognition of bondage, release, or denied dependency" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theTower) =
  cardMeaning "Collapse of false structure, shock, revelation" "Avoided upheaval, internal crisis, or delayed collapse" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theStar) =
  cardMeaning "Hope, renewal, openness, orientation after crisis" "Discouragement, disconnection, or loss of faith" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theMoon) =
  cardMeaning "Ambiguity, dream, fear, unconscious material" "Confusion lifting or deeper self-deception" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theSun) =
  cardMeaning "Vitality, clarity, joy, exposure, success" "Diminished joy, overconfidence, or delayed success" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.judgement) =
  cardMeaning "Reckoning, awakening, answering a call, reassessment" "Self-condemnation, refusal of the call, or avoidance" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.major Tarot.theWorld) =
  cardMeaning "Completion, integration, arrival, wholeness" "Incompletion, loose ends, or inability to close a cycle" regimeScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.aceR)) =
  cardMeaning "Inspiration, creative spark, new desire" "Delay, low energy, or unrealised idea" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.twoR)) =
  cardMeaning "Planning, choosing a direction, future vision" "Fear of the unknown or weak planning" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.threeR)) =
  cardMeaning "Expansion, foresight, results beginning to appear" "Delays, limited vision, or frustrated growth" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.fourR)) =
  cardMeaning "Celebration, homecoming, stability, shared achievement" "Instability, domestic tension, or private celebration" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.fiveR)) =
  cardMeaning "Competition, friction, testing oneself" "Suppressed conflict, chaos, or conflict avoidance" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.sixR)) =
  cardMeaning "Recognition, victory, confidence, public success" "Ego, lack of recognition, or fall from favour" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.sevenR)) =
  cardMeaning "Defending a position, courage under pressure" "Overwhelm, defensiveness, or giving up" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.eightR)) =
  cardMeaning "Speed, communication, movement, rapid development" "Delay, scattered action, or miscommunication" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.nineR)) =
  cardMeaning "Resilience, boundaries, persistence after injury" "Exhaustion, hypervigilance, or brittle defence" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.pip Tarot.tenR)) =
  cardMeaning "Burden, responsibility, carrying too much" "Delegation, release, or collapse under pressure" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.court Tarot.pageR)) =
  cardMeaning "Curiosity, experimentation, exciting news" "Immaturity, inconsistency, or lack of direction" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.court Tarot.knightR)) =
  cardMeaning "Adventure, passionate pursuit, bold movement" "Recklessness, impatience, or unstable commitment" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.court Tarot.queenR)) =
  cardMeaning "Confidence, warmth, independence, magnetism" "Jealousy, insecurity, or demanding attention" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.wands (Tarot.court Tarot.kingR)) =
  cardMeaning "Visionary leadership, enterprise, command" "Domineering behaviour or impulsive leadership" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.aceR)) =
  cardMeaning "Emotional opening, love, compassion, intuition" "Repressed feeling or emotional blockage" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.twoR)) =
  cardMeaning "Mutual attraction, agreement, partnership" "Imbalance, disconnection, or broken agreement" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.threeR)) =
  cardMeaning "Friendship, celebration, community, support" "Gossip, exclusion, or overindulgence" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.fourR)) =
  cardMeaning "Apathy, contemplation, withdrawal, overlooked offer" "Renewed engagement or deeper withdrawal" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.fiveR)) =
  cardMeaning "Grief, disappointment, attention fixed on loss" "Acceptance, healing, or inability to move on" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.sixR)) =
  cardMeaning "Memory, innocence, generosity, return of the past" "Idealising the past or arrested development" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.sevenR)) =
  cardMeaning "Possibility, fantasy, many attractive choices" "Confusion, unrealistic desire, or emerging clarity" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.eightR)) =
  cardMeaning "Leaving something unfulfilling, seeking deeper meaning" "Fear of leaving, avoidance, or aimless wandering" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.nineR)) =
  cardMeaning "Satisfaction, pleasure, wish fulfilled" "Smugness, excess, or outward success without fulfilment" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.pip Tarot.tenR)) =
  cardMeaning "Emotional fulfilment, family harmony, belonging" "Relational disharmony, broken ideal, or alienation" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.court Tarot.pageR)) =
  cardMeaning "Sensitivity, imaginative message, emotional discovery" "Escapism, emotional immaturity, or blocked creativity" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.court Tarot.knightR)) =
  cardMeaning "Romance, charm, idealism, following the heart" "Moodiness, fantasy, or unreliable promises" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.court Tarot.queenR)) =
  cardMeaning "Empathy, emotional depth, intuitive care" "Self-neglect, dependency, or porous boundaries" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.cups (Tarot.court Tarot.kingR)) =
  cardMeaning "Emotional balance, diplomacy, compassionate authority" "Emotional manipulation, suppression, or volatility" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.aceR)) =
  cardMeaning "Clarity, truth, decisive insight, intellectual breakthrough" "Confusion, false certainty, or misuse of truth" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.twoR)) =
  cardMeaning "Stalemate, protected indecision, blocked choice" "Overload, denial breaking down, or forced decision" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.threeR)) =
  cardMeaning "Heartbreak, grief, painful truth, separation" "Recovery, forgiveness, or lingering sorrow" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.fourR)) =
  cardMeaning "Rest, retreat, recovery, mental stillness" "Burnout, restlessness, or returning too soon" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.fiveR)) =
  cardMeaning "Hostility, self-interest, victory that costs too much" "Reconciliation, remorse, or concealed resentment" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.sixR)) =
  cardMeaning "Transition, departure, moving through difficulty" "Inability to move on or carrying unresolved baggage" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.sevenR)) =
  cardMeaning "Strategy, secrecy, evasion, acting independently" "Confession, exposure, or self-deception" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.eightR)) =
  cardMeaning "Restriction, helplessness, imprisonment by belief" "Release, new perspective, or reclaiming agency" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.nineR)) =
  cardMeaning "Anxiety, guilt, insomnia, catastrophic thought" "Recovery or anxiety becoming entrenched" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.pip Tarot.tenR)) =
  cardMeaning "Painful ending, betrayal, collapse, finality" "Survival, recovery, or refusal to accept an ending" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.court Tarot.pageR)) =
  cardMeaning "Vigilance, curiosity, questioning, sharp communication" "Gossip, cynicism, spying, or poorly directed thought" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.court Tarot.knightR)) =
  cardMeaning "Decisive action, urgency, intellectual force" "Aggression, recklessness, or charging without context" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.court Tarot.queenR)) =
  cardMeaning "Discernment, independence, honesty, clear boundaries" "Bitterness, cruelty, or excessive detachment" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.swords (Tarot.court Tarot.kingR)) =
  cardMeaning "Logic, judgement, expertise, principled authority" "Cold domination, rationalisation, or abuse of authority" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.aceR)) =
  cardMeaning "Material opportunity, grounded beginning, new resource" "Missed opportunity, insecurity, or poor foundation" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.twoR)) =
  cardMeaning "Juggling demands, adaptability, resource management" "Overload, disorganisation, or unstable priorities" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.threeR)) =
  cardMeaning "Teamwork, craft, learning, competent collaboration" "Poor cooperation, low standards, or ignored expertise" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.fourR)) =
  cardMeaning "Security, conservation, possession, control" "Greed and rigidity or releasing one's grip" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.fiveR)) =
  cardMeaning "Hardship, exclusion, illness, or material insecurity" "Recovery, finding assistance, or improving conditions" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.sixR)) =
  cardMeaning "Giving and receiving, support, unequal resources" "Conditional generosity, debt, or exploitation" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.sevenR)) =
  cardMeaning "Patience, investment, assessment of long-term work" "Impatience, poor return, or abandoning work too early" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.eightR)) =
  cardMeaning "Practice, diligence, apprenticeship, mastery through repetition" "Perfectionism, tedious labour, or careless workmanship" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.nineR)) =
  cardMeaning "Independence, earned comfort, cultivated environment" "Dependence, status anxiety, or costly self-sufficiency" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.pip Tarot.tenR)) =
  cardMeaning "Legacy, family resources, enduring material structure" "Family conflict, unstable inheritance, or short-termism" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.court Tarot.pageR)) =
  cardMeaning "Study, practical opportunity, new skill or project" "Procrastination, poor planning, or lack of application" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.court Tarot.knightR)) =
  cardMeaning "Reliability, routine, patience, steady progress" "Stagnation, stubbornness, or labour without purpose" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.court Tarot.queenR)) =
  cardMeaning "Practical nurture, resourcefulness, embodied abundance" "Self-neglect, possessiveness, or material preoccupation" localProcessScale riderWaiteSmithSemanticReceipt
meaning (Tarot.minor Tarot.pentacles (Tarot.court Tarot.kingR)) =
  cardMeaning "Material mastery, stewardship, dependable success" "Greed, rigidity, or defining worth through possession" localProcessScale riderWaiteSmithSemanticReceipt

------------------------------------------------------------------------
-- Compositional Minor Arcana surface.
------------------------------------------------------------------------

suitDomain : Tarot.Suit → String
suitDomain Tarot.wands =
  "action, desire, creativity, initiative, vocation, and conflict of wills"
suitDomain Tarot.cups =
  "emotion, relationship, imagination, memory, and receptivity"
suitDomain Tarot.swords =
  "thought, truth, language, decision, separation, and conflict"
suitDomain Tarot.pentacles =
  "matter, work, resources, body, security, and stewardship"

pipPhase : Tarot.PipRank → String
pipPhase Tarot.aceR = "seed or emergence"
pipPhase Tarot.twoR = "duality, balance, or choice"
pipPhase Tarot.threeR = "development and interaction"
pipPhase Tarot.fourR = "stability or containment"
pipPhase Tarot.fiveR = "disruption or difficulty"
pipPhase Tarot.sixR = "adjustment, exchange, or passage"
pipPhase Tarot.sevenR = "test, evaluation, or complexity"
pipPhase Tarot.eightR = "movement, constraint, or mastery"
pipPhase Tarot.nineR = "maturation and near-completion"
pipPhase Tarot.tenR = "culmination, excess, or completed cycle"

courtMode : Tarot.CourtRank → String
courtMode Tarot.pageR = "learning, noticing, or receiving"
courtMode Tarot.knightR = "pursuing or mobilising"
courtMode Tarot.queenR = "embodying and internally governing"
courtMode Tarot.kingR = "directing and externally governing"

rankFunction : Tarot.MinorRank → String
rankFunction (Tarot.pip rank) = pipPhase rank
rankFunction (Tarot.court rank) = courtMode rank

record MinorComposition : Set where
  constructor minorComposition
  field
    compositionDomain : String
    compositionPhaseOrAgency : String
    specificRange : CardMeaning

open MinorComposition public

composeMinor :
  (suit : Tarot.Suit) →
  (rank : Tarot.MinorRank) →
  MinorComposition
composeMinor suit rank =
  minorComposition
    (suitDomain suit)
    (rankFunction rank)
    (meaning (Tarot.minor suit rank))

------------------------------------------------------------------------
-- Orientation supplies an interpretive lens, not a truth-value flip.
------------------------------------------------------------------------

record OrientedMeaning : Set where
  constructor orientedMeaning
  field
    baseRange : CardMeaning
    activeText : String
    possibleReversalLenses : List ReversalMode
    orientationReceipt : String

open OrientedMeaning public

meaningFor : Tarot.CardToken → OrientedMeaning
meaningFor token with Tarot.orientation token
... | Tarot.uprightOrientation =
  orientedMeaning
    (meaning (Tarot.cardIdentity token))
    (centralMeaning (meaning (Tarot.cardIdentity token)))
    []
    "upright range selected"
... | Tarot.reversedOrientation =
  orientedMeaning
    (meaning (Tarot.cardIdentity token))
    (shadowOrReversal (meaning (Tarot.cardIdentity token)))
    (blocked ∷ internalised ∷ excessive ∷ deficient ∷ distorted ∷ releasing ∷ [])
    "reversal may express blockage, internalisation, excess, deficiency, distortion, or release"

deathCentralMeaningIsTransformation :
  centralMeaning (meaning (Tarot.major Tarot.death))
  ≡ "Ending, irreversible transformation, clearing away"
deathCentralMeaningIsTransformation = refl

towerShadowRetainsDelayedCollapse :
  shadowOrReversal (meaning (Tarot.major Tarot.theTower))
  ≡ "Avoided upheaval, internal crisis, or delayed collapse"
towerShadowRetainsDelayedCollapse = refl

knightOfCupsCompositionIsPursuitInEmotionalDomain :
  compositionDomain
    (composeMinor Tarot.cups (Tarot.court Tarot.knightR))
  ≡ "emotion, relationship, imagination, memory, and receptivity"
  ×
  compositionPhaseOrAgency
    (composeMinor Tarot.cups (Tarot.court Tarot.knightR))
  ≡ "pursuing or mobilising"
knightOfCupsCompositionIsPursuitInEmotionalDomain = refl , refl

record TarotSemanticBoundary : Set where
  constructor tarotSemanticBoundary
  field
    allSeventyEightCardsHaveRanges : Bool
    cardRangeIsOneTrueSentence : Bool
    reversalIsLogicalNegation : Bool
    illustratedSceneMayRefineRankMnemonic : Bool
    semanticRangeIsClinicalDiagnosis : Bool

canonicalTarotSemanticBoundary : TarotSemanticBoundary
canonicalTarotSemanticBoundary =
  tarotSemanticBoundary true false false true false
