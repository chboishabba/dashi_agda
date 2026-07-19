module DASHI.Biology.PredictiveMetastabilityTraumaBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Predictive-processing trauma bridge.
--
-- This module sharpens the earlier body-memory vocabulary.  It keeps the
-- useful DASHI reading -- old inverse / residual / +1 -- but blocks the
-- stronger literal claim that trauma is stored as hidden content in body
-- tissue.  The body is tracked as messenger/display surface for recurrent
-- inference, not as a sovereign archive.
--
-- The metastability/flow row is explicitly candidate-only: it records the
-- proposed bridge from flow states to restored chart mobility without
-- promoting a clinical theorem, treatment protocol, diagnosis, or cure.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Surfaces.

data PredictiveTraumaSurface : Set where
  dangerPriorPrecisionSurface :
    PredictiveTraumaSurface

  freeEnergyLocalMinimumSurface :
    PredictiveTraumaSurface

  metastableChartMobilitySurface :
    PredictiveTraumaSurface

  interoceptiveMessengerSurface :
    PredictiveTraumaSurface

  flowRestoresApproachSurface :
    PredictiveTraumaSurface

  recoveredMemoryBoundarySurface :
    PredictiveTraumaSurface

canonicalPredictiveTraumaSurfaces :
  List PredictiveTraumaSurface
canonicalPredictiveTraumaSurfaces =
  dangerPriorPrecisionSurface
  ∷ freeEnergyLocalMinimumSurface
  ∷ metastableChartMobilitySurface
  ∷ interoceptiveMessengerSurface
  ∷ flowRestoresApproachSurface
  ∷ recoveredMemoryBoundarySurface
  ∷ []

canonicalPredictiveTraumaSurfaceCount : Nat
canonicalPredictiveTraumaSurfaceCount =
  listCount canonicalPredictiveTraumaSurfaces

predictiveTraumaSurfaceName :
  PredictiveTraumaSurface → String
predictiveTraumaSurfaceName dangerPriorPrecisionSurface =
  "over-precise danger prior"
predictiveTraumaSurfaceName freeEnergyLocalMinimumSurface =
  "threat local minimum in a free-energy landscape"
predictiveTraumaSurfaceName metastableChartMobilitySurface =
  "metastable chart mobility"
predictiveTraumaSurfaceName interoceptiveMessengerSurface =
  "interoceptive body messenger"
predictiveTraumaSurfaceName flowRestoresApproachSurface =
  "flow as safe-arousal approach repair candidate"
predictiveTraumaSurfaceName recoveredMemoryBoundarySurface =
  "recovered-memory and somatic-sovereignty boundary"

predictiveTraumaSurfaceReading :
  PredictiveTraumaSurface → String
predictiveTraumaSurfaceReading dangerPriorPrecisionSurface =
  "Trauma is modeled as a candidate over-weighting of threat priors, not as literal body-tissue storage."
predictiveTraumaSurfaceReading freeEnergyLocalMinimumSurface =
  "The threat chart is treated as a local minimum with excessive update authority."
predictiveTraumaSurfaceReading metastableChartMobilitySurface =
  "Health is read as mobility among semi-stable charts; PTSD-like rigidity is read as reduced chart repertoire."
predictiveTraumaSurfaceReading interoceptiveMessengerSurface =
  "Body sensations are evidence streams interpreted by a predictive model; they are not sovereign recovered truth."
predictiveTraumaSurfaceReading flowRestoresApproachSurface =
  "Flow is a candidate +1: safe arousal plus feedback plus agency may restore approach dynamics."
predictiveTraumaSurfaceReading recoveredMemoryBoundarySurface =
  "No somatic or narrative signal is promoted to forced disclosure, diagnosis, or factual memory authority."

------------------------------------------------------------------------
-- Bridge receipt.

record PredictiveMetastabilityTraumaBridge : Set where
  constructor mkPredictiveMetastabilityTraumaBridge
  field
    bridgeSurfaces :
      List PredictiveTraumaSurface

    bridgeSurfacesAreCanonical :
      bridgeSurfaces ≡ canonicalPredictiveTraumaSurfaces

    bodyArchiveClaim :
      Bool

    bodyArchiveClaimIsFalse :
      bodyArchiveClaim ≡ false

    bodyMessengerClaim :
      Bool

    bodyMessengerClaimIsTrue :
      bodyMessengerClaim ≡ true

    predictiveScoreClaim :
      Bool

    predictiveScoreClaimIsTrue :
      predictiveScoreClaim ≡ true

    overPreciseDangerPriorTracked :
      Bool

    overPreciseDangerPriorTrackedIsTrue :
      overPreciseDangerPriorTracked ≡ true

    metastabilityHypothesisTracked :
      Bool

    metastabilityHypothesisTrackedIsTrue :
      metastabilityHypothesisTracked ≡ true

    metastabilityClinicalTheoremPromoted :
      Bool

    metastabilityClinicalTheoremPromotedIsFalse :
      metastabilityClinicalTheoremPromoted ≡ false

    flowTreatmentProtocolPromoted :
      Bool

    flowTreatmentProtocolPromotedIsFalse :
      flowTreatmentProtocolPromoted ≡ false

    diagnosisPromoted :
      Bool

    diagnosisPromotedIsFalse :
      diagnosisPromoted ≡ false

    recoveredMemoryAuthorityPromoted :
      Bool

    recoveredMemoryAuthorityPromotedIsFalse :
      recoveredMemoryAuthorityPromoted ≡ false

    bridgeReading :
      String

open PredictiveMetastabilityTraumaBridge public

canonicalPredictiveMetastabilityTraumaBridge :
  PredictiveMetastabilityTraumaBridge
canonicalPredictiveMetastabilityTraumaBridge =
  mkPredictiveMetastabilityTraumaBridge
    canonicalPredictiveTraumaSurfaces
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "The nervous system keeps predicting the score and the body displays the prediction; trauma is modeled as stuck inference / reduced chart mobility, while flow repair remains candidate-only."

canonicalBodyArchiveClaimFalse :
  bodyArchiveClaim canonicalPredictiveMetastabilityTraumaBridge ≡ false
canonicalBodyArchiveClaimFalse =
  bodyArchiveClaimIsFalse canonicalPredictiveMetastabilityTraumaBridge

canonicalBodyMessengerClaimTrue :
  bodyMessengerClaim canonicalPredictiveMetastabilityTraumaBridge ≡ true
canonicalBodyMessengerClaimTrue =
  bodyMessengerClaimIsTrue canonicalPredictiveMetastabilityTraumaBridge

canonicalPredictiveScoreClaimTrue :
  predictiveScoreClaim canonicalPredictiveMetastabilityTraumaBridge ≡ true
canonicalPredictiveScoreClaimTrue =
  predictiveScoreClaimIsTrue canonicalPredictiveMetastabilityTraumaBridge

canonicalMetastabilityClinicalTheoremPromotedFalse :
  metastabilityClinicalTheoremPromoted canonicalPredictiveMetastabilityTraumaBridge ≡ false
canonicalMetastabilityClinicalTheoremPromotedFalse =
  metastabilityClinicalTheoremPromotedIsFalse canonicalPredictiveMetastabilityTraumaBridge

canonicalRecoveredMemoryAuthorityPromotedFalse :
  recoveredMemoryAuthorityPromoted canonicalPredictiveMetastabilityTraumaBridge ≡ false
canonicalRecoveredMemoryAuthorityPromotedFalse =
  recoveredMemoryAuthorityPromotedIsFalse canonicalPredictiveMetastabilityTraumaBridge
