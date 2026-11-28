module DASHI.Reasoning.X369SophonticSpiralRetainedTransportExact where

-- DASHI extension; reuse actual dialectical spiral and irreducible face.
-- Original Leech-LILA: Anatolii Kornienko.
-- Semantic interventions are independently licensed by the source.
-- No identification of argument opposition with sign or antipode.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
import DASHI.Biology.DialecticalSheetSpiralExact as Spiral
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Cognition.PNF.X369WholeSourceIndexedTransportExact as Whole

record ReasoningContext (Evidence Indices : Set) : Set where
  constructor context
  field
    spiral : Spiral.SpiralState
    triadic : Face.TrialecticState
    evidence : Evidence
    indices : Indices

open ReasoningContext public

rotateContext : ∀ {E I : Set} → ReasoningContext E I → ReasoningContext E I
rotateContext (context s t e i) = context (Spiral.liftRotation s) t e i

reflectContext : ∀ {E I : Set} → ReasoningContext E I → ReasoningContext E I
reflectContext (context s t e i) = context (Spiral.liftReflection s) t e i

fourTurns : ∀ {E I : Set} → ReasoningContext E I → ReasoningContext E I
fourTurns x = rotateContext (rotateContext (rotateContext (rotateContext x)))

sheetReturns : ∀ {E I : Set} (x : ReasoningContext E I) →
  Spiral.projectedSheet (spiral (fourTurns x)) ≡ Spiral.projectedSheet (spiral x)
sheetReturns (context s t e i) = Spiral.projectedReturnAfterFour s

heightAdvances : ∀ {E I : Set} (x : ReasoningContext E I) →
  Spiral.historicalHeight (spiral (fourTurns x)) ≡
  suc (suc (suc (suc (Spiral.historicalHeight (spiral x)))))
heightAdvances (context s t e i) = Spiral.historicalLiftAfterFour s

reflectionReversesSense : ∀ {E I : Set} (x : ReasoningContext E I) →
  Spiral.spiralSense (spiral (reflectContext x)) ≡
  Spiral.flipSense (Spiral.spiralSense (spiral x))
reflectionReversesSense (context s t e i) = Spiral.reflectionFlipsSpiralSense s

rotationDoesNotEraseEvidence : ∀ {E I : Set} (x : ReasoningContext E I) →
  evidence (fourTurns x) ≡ evidence x
rotationDoesNotEraseEvidence (context (Spiral.spiralState s h k) t e i) = refl

rotationDoesNotDetermineFace : ∀ {E I : Set} (x : ReasoningContext E I) →
  triadic (fourTurns x) ≡ triadic x
rotationDoesNotDetermineFace (context (Spiral.spiralState s h k) t e i) = refl

-- Same sheet / same three dyads / same evidence can still carry different
-- triadic face. Source-valid examples require independent evidence.
faceCannotFactorThroughBoundary :
  (read : Face.TrialecticBoundary → Face.TriadicFaceRelation) →
  ((x : Face.TrialecticState) → read (Face.boundary x) ≡ Face.face x) →
  ⊥
faceCannotFactorThroughBoundary read exact
  with exact Face.sameEdgesReciprocal | exact Face.sameEdgesCoercive
... | p | q = Face.differentTriadicFace (join p q)
  where
    join : ∀ {A : Set} {x y z : A} → x ≡ y → x ≡ z → y ≡ z
    join refl r = r

-- Compose the original neural execution and independently owned reasoning
-- evolution with the existing all-word exact retraction proof.
module RetainedReasoner
  (H C Evidence Indices U O : Set)
  (encode : H → C)
  (decode : C → H)
  (decodeEncode : (h : H) → decode (encode h) ≡ h)
  (step : U → H → H)
  (observe : U → H → O)
  (governedReasoningStep : U → ReasoningContext Evidence Indices →
                              ReasoningContext Evidence Indices) where

  module Transport = Whole.ExactTransport H C
    (ReasoningContext Evidence Indices) U O
    encode decode decodeEncode step observe governedReasoningStep

  fullReasoningAndNeuralReopen = Transport.exactJointReopen
  originalNeuralStepSquare = Transport.sourceStepSquare
  originalReadoutSquare = Transport.sourceObserveSquare
  allWordRetainedEndpoint = Transport.everyPacketEndpoint
  allWordOriginalReadout = Transport.everyOriginalReadout
  independentReasoningStateReopens = Transport.independentContextReopens

-- Real source semantic action, time/refinement/authority transitions and
-- E8/Leech action on the actual source are separate supplied operations.
-- Kernel intentionally deferred.
