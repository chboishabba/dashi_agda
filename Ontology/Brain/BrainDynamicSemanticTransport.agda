module Ontology.Brain.BrainDynamicSemanticTransport where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.Brain.BrainVisualFormConstantSurface as Visual
import Ontology.Brain.BrainLearningEigenbasisSurface as Learn
import Ontology.Brain.BrainInvariantSemanticLaws as Semantic
import Ontology.Brain.BrainMorphospaceGapJunctionSurface as Morph

------------------------------------------------------------------------
-- Local dynamic semantic transport for the four brain theme owners.
--
-- This is intentionally theorem-thin and non-claiming.  Time is a phantom
-- index, transports are bounded local morphisms, and semantic drift is
-- exposed only against the coarse invariant semantic already owned locally.

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

data ⊥ : Set where

zero≠suc : zero ≡ suc zero → ⊥
zero≠suc ()

BrainTime : Set
BrainTime = Nat

BrainDt : Set
BrainDt = Nat

data BrainDriftToleranceName : Set where
  brainSemanticDriftToleranceName : BrainDriftToleranceName

brainSemanticDriftTolerance : Nat
brainSemanticDriftTolerance = suc zero

semanticDistance :
  Semantic.BrainInvariantSemantic →
  Semantic.BrainInvariantSemantic →
  Nat
semanticDistance Semantic.quiescent Semantic.quiescent = zero
semanticDistance Semantic.quiescent Semantic.engaged = suc zero
semanticDistance Semantic.engaged Semantic.quiescent = suc zero
semanticDistance Semantic.engaged Semantic.engaged = zero

semanticDistance-self :
  (sem : Semantic.BrainInvariantSemantic) →
  semanticDistance sem sem ≡ zero
semanticDistance-self Semantic.quiescent = refl
semanticDistance-self Semantic.engaged = refl

record BrainBoundedSemanticDrift : Set where
  constructor boundedSemanticDrift
  field
    drift : Nat
    tolerance : Nat
    withinTolerance : drift ≤ tolerance

zeroDriftBounded :
  BrainBoundedSemanticDrift
zeroDriftBounded =
  boundedSemanticDrift zero brainSemanticDriftTolerance z≤n

record BrainRegionThemeAt (n : Nat) (t : BrainTime) : Set where
  constructor brainRegionThemeAt
  field
    carrier : BrainState n
    region : Region.BrainRegion
    regionState : Region.BrainRegionState n

record BrainVisualThemeAt (n : Nat) (t : BrainTime) : Set where
  constructor brainVisualThemeAt
  field
    carrier : BrainState n
    geometry : Visual.BrainLogPolarGeometry
    formConstant : Visual.BrainVisualFormConstant

record BrainLearningThemeAt (n : Nat) (t : BrainTime) : Set where
  constructor brainLearningThemeAt
  field
    carrier : BrainState n
    profile : Learn.BrainLearningEigenbasisProfile
    phase : Learn.BrainRepresentationPhase

record BrainMorphospaceThemeAt (n : Nat) (t : BrainTime) : Set where
  constructor brainMorphospaceThemeAt
  field
    carrier : BrainState n
    point : Morph.BrainMorphospacePoint

regionThemeAt :
  ∀ {n t} → BrainState n → Region.BrainRegion → BrainRegionThemeAt n t
regionThemeAt st r =
  brainRegionThemeAt st r (Region.regionStateOf st r)

visualThemeAt :
  ∀ {n t} → BrainState n → BrainVisualThemeAt n t
visualThemeAt st =
  brainVisualThemeAt st (Visual.geometryOfState st) (Visual.classifyState st)

learningThemeAt :
  ∀ {n t} → BrainState n → BrainLearningThemeAt n t
learningThemeAt st =
  brainLearningThemeAt st (Learn.profileOfState st) (Learn.phaseOfState st)

morphospaceThemeAt :
  ∀ {n t} → BrainState n → BrainMorphospaceThemeAt n t
morphospaceThemeAt st =
  brainMorphospaceThemeAt st (Morph.morphospaceOfState st)

regionThemeSemantic :
  ∀ {n t} → BrainRegionThemeAt n t → Semantic.BrainInvariantSemantic
regionThemeSemantic theme =
  Semantic.semanticOfState (BrainRegionThemeAt.carrier theme)

visualThemeSemantic :
  ∀ {n t} → BrainVisualThemeAt n t → Semantic.BrainInvariantSemantic
visualThemeSemantic theme =
  Semantic.semanticOfState (BrainVisualThemeAt.carrier theme)

learningThemeSemantic :
  ∀ {n t} → BrainLearningThemeAt n t → Semantic.BrainInvariantSemantic
learningThemeSemantic theme =
  Semantic.semanticOfState (BrainLearningThemeAt.carrier theme)

morphospaceThemeSemantic :
  ∀ {n t} → BrainMorphospaceThemeAt n t → Semantic.BrainInvariantSemantic
morphospaceThemeSemantic theme =
  Morph.BrainMorphospacePoint.semantic (BrainMorphospaceThemeAt.point theme)

TdynRegion :
  ∀ {n t} → (dt : BrainDt) → BrainRegionThemeAt n t → BrainRegionThemeAt n (t + dt)
TdynRegion dt theme =
  brainRegionThemeAt
    (BrainRegionThemeAt.carrier theme)
    (Region.stepRegion (BrainRegionThemeAt.region theme))
    (Region.regionStateOf
      (BrainRegionThemeAt.carrier theme)
      (Region.stepRegion (BrainRegionThemeAt.region theme)))

TdynVisual :
  ∀ {n t} → (dt : BrainDt) → BrainVisualThemeAt n t → BrainVisualThemeAt n (t + dt)
TdynVisual dt theme =
  brainVisualThemeAt
    (BrainVisualThemeAt.carrier theme)
    (Visual.geometryOfState (BrainVisualThemeAt.carrier theme))
    (Visual.classifyState (BrainVisualThemeAt.carrier theme))

TdynLearning :
  ∀ {n t} → (dt : BrainDt) → BrainLearningThemeAt n t → BrainLearningThemeAt n (t + dt)
TdynLearning dt theme =
  brainLearningThemeAt
    (BrainLearningThemeAt.carrier theme)
    (Learn.profileOfState (BrainLearningThemeAt.carrier theme))
    (Learn.phaseOfState (BrainLearningThemeAt.carrier theme))

TdynMorphospace :
  ∀ {n t} →
  (dt : BrainDt) → BrainMorphospaceThemeAt n t → BrainMorphospaceThemeAt n (t + dt)
TdynMorphospace dt theme =
  brainMorphospaceThemeAt
    (BrainMorphospaceThemeAt.carrier theme)
    (Morph.recursiveCorrectMorphospace (BrainMorphospaceThemeAt.point theme))

regionDynamicSemanticDrift :
  ∀ {n t} → (dt : BrainDt) → BrainRegionThemeAt n t → Nat
regionDynamicSemanticDrift dt theme =
  semanticDistance
    (regionThemeSemantic theme)
    (regionThemeSemantic (TdynRegion dt theme))

visualDynamicSemanticDrift :
  ∀ {n t} → (dt : BrainDt) → BrainVisualThemeAt n t → Nat
visualDynamicSemanticDrift dt theme =
  semanticDistance
    (visualThemeSemantic theme)
    (visualThemeSemantic (TdynVisual dt theme))

learningDynamicSemanticDrift :
  ∀ {n t} → (dt : BrainDt) → BrainLearningThemeAt n t → Nat
learningDynamicSemanticDrift dt theme =
  semanticDistance
    (learningThemeSemantic theme)
    (learningThemeSemantic (TdynLearning dt theme))

morphospaceDynamicSemanticDrift :
  ∀ {n t} → (dt : BrainDt) → BrainMorphospaceThemeAt n t → Nat
morphospaceDynamicSemanticDrift dt theme =
  semanticDistance
    (morphospaceThemeSemantic theme)
    (morphospaceThemeSemantic (TdynMorphospace dt theme))

regionDynamicSemanticDrift-zero :
  ∀ {n t} (dt : BrainDt) (theme : BrainRegionThemeAt n t) →
  regionDynamicSemanticDrift dt theme ≡ zero
regionDynamicSemanticDrift-zero dt theme =
  semanticDistance-self (regionThemeSemantic theme)

visualDynamicSemanticDrift-zero :
  ∀ {n t} (dt : BrainDt) (theme : BrainVisualThemeAt n t) →
  visualDynamicSemanticDrift dt theme ≡ zero
visualDynamicSemanticDrift-zero dt theme =
  semanticDistance-self (visualThemeSemantic theme)

learningDynamicSemanticDrift-zero :
  ∀ {n t} (dt : BrainDt) (theme : BrainLearningThemeAt n t) →
  learningDynamicSemanticDrift dt theme ≡ zero
learningDynamicSemanticDrift-zero dt theme =
  semanticDistance-self (learningThemeSemantic theme)

morphospaceDynamicSemanticDrift-zero :
  ∀ {n t} (dt : BrainDt) (theme : BrainMorphospaceThemeAt n t) →
  morphospaceDynamicSemanticDrift dt theme ≡ zero
morphospaceDynamicSemanticDrift-zero dt theme =
  semanticDistance-self (morphospaceThemeSemantic theme)

regionDynamicSemanticDriftBound :
  ∀ {n t} (dt : BrainDt) (theme : BrainRegionThemeAt n t) →
  BrainBoundedSemanticDrift
regionDynamicSemanticDriftBound dt theme = zeroDriftBounded

visualDynamicSemanticDriftBound :
  ∀ {n t} (dt : BrainDt) (theme : BrainVisualThemeAt n t) →
  BrainBoundedSemanticDrift
visualDynamicSemanticDriftBound dt theme = zeroDriftBounded

learningDynamicSemanticDriftBound :
  ∀ {n t} (dt : BrainDt) (theme : BrainLearningThemeAt n t) →
  BrainBoundedSemanticDrift
learningDynamicSemanticDriftBound dt theme = zeroDriftBounded

morphospaceDynamicSemanticDriftBound :
  ∀ {n t} (dt : BrainDt) (theme : BrainMorphospaceThemeAt n t) →
  BrainBoundedSemanticDrift
morphospaceDynamicSemanticDriftBound dt theme = zeroDriftBounded

record DynamicTransportMorphism (ThemeAt : BrainTime → Set) : Set₁ where
  constructor dynamicTransportMorphism
  field
    transport : ∀ {t} → (dt : BrainDt) → ThemeAt t → ThemeAt (t + dt)
    driftBound : ∀ {t} → (dt : BrainDt) → ThemeAt t → BrainBoundedSemanticDrift

regionDynamicTransport :
  ∀ {n} → DynamicTransportMorphism (BrainRegionThemeAt n)
regionDynamicTransport = dynamicTransportMorphism TdynRegion regionDynamicSemanticDriftBound

visualDynamicTransport :
  ∀ {n} → DynamicTransportMorphism (BrainVisualThemeAt n)
visualDynamicTransport = dynamicTransportMorphism TdynVisual visualDynamicSemanticDriftBound

learningDynamicTransport :
  ∀ {n} → DynamicTransportMorphism (BrainLearningThemeAt n)
learningDynamicTransport =
  dynamicTransportMorphism TdynLearning learningDynamicSemanticDriftBound

morphospaceDynamicTransport :
  ∀ {n} → DynamicTransportMorphism (BrainMorphospaceThemeAt n)
morphospaceDynamicTransport =
  dynamicTransportMorphism TdynMorphospace morphospaceDynamicSemanticDriftBound

record IndependentThemeConsumers (n : Nat) (t : BrainTime) : Set where
  constructor independentThemeConsumers
  field
    regionTheme : BrainRegionThemeAt n t
    visualTheme : BrainVisualThemeAt n t
    learningTheme : BrainLearningThemeAt n t
    morphospaceTheme : BrainMorphospaceThemeAt n t

independentThemeConsumersOf :
  ∀ {n t} → BrainState n → Region.BrainRegion → IndependentThemeConsumers n t
independentThemeConsumersOf st r =
  independentThemeConsumers
    (regionThemeAt st r)
    (visualThemeAt st)
    (learningThemeAt st)
    (morphospaceThemeAt st)

jointCrossThemeCoherence :
  ∀ {n t} → IndependentThemeConsumers n t → Nat
jointCrossThemeCoherence consumers =
  Region.motifIndex
    (Region.motifOf
      (BrainRegionThemeAt.region
        (IndependentThemeConsumers.regionTheme consumers)))
  +
  Visual.BrainLogPolarGeometry.radialRing
    (BrainVisualThemeAt.geometry
      (IndependentThemeConsumers.visualTheme consumers))
  +
  Learn.BrainLearningEigenbasisProfile.width
    (BrainLearningThemeAt.profile
      (IndependentThemeConsumers.learningTheme consumers))
  +
  Morph.BrainMorphospacePoint.depth
    (BrainMorphospaceThemeAt.point
      (IndependentThemeConsumers.morphospaceTheme consumers))

record BrainJointSemanticConsumer (n : Nat) (t : BrainTime) : Set where
  constructor brainJointSemanticConsumer
  field
    independentView : IndependentThemeConsumers n t
    jointSemantic : Semantic.BrainInvariantSemantic
    crossThemeCoherence : Nat
    driftTolerance : Nat

κ :
  ∀ {n t} → BrainState n → Region.BrainRegion → BrainJointSemanticConsumer n t
κ st r =
  brainJointSemanticConsumer
    consumers
    (Semantic.semanticOfState st)
    (jointCrossThemeCoherence consumers)
    brainSemanticDriftTolerance
  where
    consumers = independentThemeConsumersOf st r

forgetJoint :
  ∀ {n t} → BrainJointSemanticConsumer n t → IndependentThemeConsumers n t
forgetJoint joint =
  BrainJointSemanticConsumer.independentView joint

jointWithCoherence :
  ∀ {n t} →
  IndependentThemeConsumers n t →
  Semantic.BrainInvariantSemantic →
  Nat →
  BrainJointSemanticConsumer n t
jointWithCoherence consumers sem coherence =
  brainJointSemanticConsumer
    consumers
    sem
    coherence
    brainSemanticDriftTolerance

record StrictRicherJointConsumerWitness (n : Nat) (t : BrainTime) : Set where
  constructor strictRicherJointConsumerWitness
  field
    independentView : IndependentThemeConsumers n t
    leftJoint : BrainJointSemanticConsumer n t
    rightJoint : BrainJointSemanticConsumer n t
    sameIndependentProjection : forgetJoint leftJoint ≡ forgetJoint rightJoint
    differentExtraCoherence :
      BrainJointSemanticConsumer.crossThemeCoherence leftJoint
        ≡
      BrainJointSemanticConsumer.crossThemeCoherence rightJoint →
      ⊥

strictRicherThanIndependent :
  ∀ {n t} →
  IndependentThemeConsumers n t →
  Semantic.BrainInvariantSemantic →
  StrictRicherJointConsumerWitness n t
strictRicherThanIndependent consumers sem =
  strictRicherJointConsumerWitness
    consumers
    (jointWithCoherence consumers sem zero)
    (jointWithCoherence consumers sem (suc zero))
    refl
    zero≠suc

κ-strict-richer-witness :
  ∀ {n t} → BrainState n → Region.BrainRegion → StrictRicherJointConsumerWitness n t
κ-strict-richer-witness st r =
  strictRicherThanIndependent
    (independentThemeConsumersOf st r)
    (Semantic.semanticOfState st)

allFourBrainThemesRepresented : Nat
allFourBrainThemesRepresented = 4

record BrainDynamicSemanticTransportSurface : Setω where
  field
    regionSurface : Region.BrainRegionAutomatonSurface
    visualSurface : Visual.BrainVisualFormConstantSurface
    learningSurface : Learn.BrainLearningEigenbasisSurface
    morphospaceSurface : Morph.BrainMorphospaceGapJunctionSurface

    driftToleranceName : BrainDriftToleranceName
    driftToleranceValue : Nat
    representedThemeCount : Nat

    regionTdyn : ∀ {n} → DynamicTransportMorphism (BrainRegionThemeAt n)
    visualTdyn : ∀ {n} → DynamicTransportMorphism (BrainVisualThemeAt n)
    learningTdyn : ∀ {n} → DynamicTransportMorphism (BrainLearningThemeAt n)
    morphospaceTdyn : ∀ {n} → DynamicTransportMorphism (BrainMorphospaceThemeAt n)

    jointConsumer :
      ∀ {n t} → BrainState n → Region.BrainRegion → BrainJointSemanticConsumer n t
    strictRicherWitness :
      ∀ {n t} →
      BrainState n → Region.BrainRegion → StrictRicherJointConsumerWitness n t

brainDynamicSemanticTransportSurface :
  BrainDynamicSemanticTransportSurface
brainDynamicSemanticTransportSurface = record
  { regionSurface = Region.brainRegionAutomatonSurface
  ; visualSurface = Visual.brainVisualFormConstantSurface
  ; learningSurface = Learn.brainLearningEigenbasisSurface
  ; morphospaceSurface = Morph.brainMorphospaceGapJunctionSurface
  ; driftToleranceName = brainSemanticDriftToleranceName
  ; driftToleranceValue = brainSemanticDriftTolerance
  ; representedThemeCount = allFourBrainThemesRepresented
  ; regionTdyn = regionDynamicTransport
  ; visualTdyn = visualDynamicTransport
  ; learningTdyn = learningDynamicTransport
  ; morphospaceTdyn = morphospaceDynamicTransport
  ; jointConsumer = κ
  ; strictRicherWitness = κ-strict-richer-witness
  }
