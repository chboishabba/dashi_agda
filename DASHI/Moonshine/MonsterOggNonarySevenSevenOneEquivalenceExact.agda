module DASHI.Moonshine.MonsterOggNonarySevenSevenOneEquivalenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the 7+7+1 count to an actual finite equivalence.  Every one of the
-- fifteen Ogg lanes is classified into exactly one of MirrorA7, MirrorB7 or
-- Sign1, and forgetting the classification is inverse in both directions.
-- The nonary address then proves that coarse sheet seven uniquely identifies
-- p71.  This is a carrier equivalence only; no linear action or invariant
-- direct-sum decomposition is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact as Probe
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

SemanticSevenSevenOneLane : Set
SemanticSevenSevenOneLane =
  Probe.MirrorA7Lane ⊎ (Probe.MirrorB7Lane ⊎ Probe.Sign1Lane)

classifyOggLane : Lane.MonsterPrimeLane → SemanticSevenSevenOneLane
classifyOggLane Lane.p2 = inj₁ Probe.mirrorA2
classifyOggLane Lane.p3 = inj₁ Probe.mirrorA3
classifyOggLane Lane.p5 = inj₁ Probe.mirrorA5
classifyOggLane Lane.p7 = inj₁ Probe.mirrorA7
classifyOggLane Lane.p11 = inj₁ Probe.mirrorA11
classifyOggLane Lane.p13 = inj₁ Probe.mirrorA13
classifyOggLane Lane.p17 = inj₁ Probe.mirrorA17
classifyOggLane Lane.p19 = inj₂ (inj₁ Probe.mirrorB19)
classifyOggLane Lane.p23 = inj₂ (inj₁ Probe.mirrorB23)
classifyOggLane Lane.p29 = inj₂ (inj₁ Probe.mirrorB29)
classifyOggLane Lane.p31 = inj₂ (inj₁ Probe.mirrorB31)
classifyOggLane Lane.p41 = inj₂ (inj₁ Probe.mirrorB41)
classifyOggLane Lane.p47 = inj₂ (inj₁ Probe.mirrorB47)
classifyOggLane Lane.p59 = inj₂ (inj₁ Probe.mirrorB59)
classifyOggLane Lane.p71 = inj₂ (inj₂ Probe.sign71)

forgetSevenSevenOneLane :
  SemanticSevenSevenOneLane → Lane.MonsterPrimeLane
forgetSevenSevenOneLane (inj₁ lane) = Probe.mirrorA7Prime lane
forgetSevenSevenOneLane (inj₂ (inj₁ lane)) = Probe.mirrorB7Prime lane
forgetSevenSevenOneLane (inj₂ (inj₂ lane)) = Probe.sign1Prime lane

forgetAfterClassify :
  (prime : Lane.MonsterPrimeLane) →
  forgetSevenSevenOneLane (classifyOggLane prime) ≡ prime
forgetAfterClassify Lane.p2 = refl
forgetAfterClassify Lane.p3 = refl
forgetAfterClassify Lane.p5 = refl
forgetAfterClassify Lane.p7 = refl
forgetAfterClassify Lane.p11 = refl
forgetAfterClassify Lane.p13 = refl
forgetAfterClassify Lane.p17 = refl
forgetAfterClassify Lane.p19 = refl
forgetAfterClassify Lane.p23 = refl
forgetAfterClassify Lane.p29 = refl
forgetAfterClassify Lane.p31 = refl
forgetAfterClassify Lane.p41 = refl
forgetAfterClassify Lane.p47 = refl
forgetAfterClassify Lane.p59 = refl
forgetAfterClassify Lane.p71 = refl

classifyAfterForget :
  (lane : SemanticSevenSevenOneLane) →
  classifyOggLane (forgetSevenSevenOneLane lane) ≡ lane
classifyAfterForget (inj₁ Probe.mirrorA2) = refl
classifyAfterForget (inj₁ Probe.mirrorA3) = refl
classifyAfterForget (inj₁ Probe.mirrorA5) = refl
classifyAfterForget (inj₁ Probe.mirrorA7) = refl
classifyAfterForget (inj₁ Probe.mirrorA11) = refl
classifyAfterForget (inj₁ Probe.mirrorA13) = refl
classifyAfterForget (inj₁ Probe.mirrorA17) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB19)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB23)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB29)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB31)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB41)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB47)) = refl
classifyAfterForget (inj₂ (inj₁ Probe.mirrorB59)) = refl
classifyAfterForget (inj₂ (inj₂ Probe.sign71)) = refl

record SevenSevenOneCarrierEquivalence : Set where
  constructor seven-seven-one-carrier-equivalence
  field
    toSevenSevenOne : Lane.MonsterPrimeLane → SemanticSevenSevenOneLane
    fromSevenSevenOne : SemanticSevenSevenOneLane → Lane.MonsterPrimeLane
    fromAfterTo :
      (prime : Lane.MonsterPrimeLane) →
      fromSevenSevenOne (toSevenSevenOne prime) ≡ prime
    toAfterFrom :
      (lane : SemanticSevenSevenOneLane) →
      toSevenSevenOne (fromSevenSevenOne lane) ≡ lane

open SevenSevenOneCarrierEquivalence public

canonicalSevenSevenOneCarrierEquivalence : SevenSevenOneCarrierEquivalence
canonicalSevenSevenOneCarrierEquivalence =
  seven-seven-one-carrier-equivalence
    classifyOggLane
    forgetSevenSevenOneLane
    forgetAfterClassify
    classifyAfterForget

------------------------------------------------------------------------
-- p71 is the unique lane in coarse sheet seven.
------------------------------------------------------------------------

coarseSheetSevenUniquelyIdentifiesP71 :
  (prime : Lane.MonsterPrimeLane) →
  Probe.coarseSheets (Probe.nonaryProbe prime) ≡ 7 →
  prime ≡ Lane.p71
coarseSheetSevenUniquelyIdentifiesP71 Lane.p2 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p3 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p5 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p7 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p11 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p13 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p17 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p19 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p23 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p29 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p31 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p41 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p47 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p59 ()
coarseSheetSevenUniquelyIdentifiesP71 Lane.p71 refl = refl

p71IsClassifiedAsSign1 :
  classifyOggLane Lane.p71 ≡ inj₂ (inj₂ Probe.sign71)
p71IsClassifiedAsSign1 = refl
