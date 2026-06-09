module DASHI.Physics.Closure.NSA9SingularityContradictionRouteBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data A9Stage : Set where
  importA8DecayStage : A9Stage
  localVorticityVanishingStage : A9Stage
  localHarmonicityStage : A9Stage
  ellipticRegularityStage : A9Stage
  singularityContradictionStage : A9Stage
  bkmGuardStage : A9Stage
  clayPromotionGuardStage : A9Stage

canonicalA9Stages : List A9Stage
canonicalA9Stages =
  importA8DecayStage
  ∷ localVorticityVanishingStage
  ∷ localHarmonicityStage
  ∷ ellipticRegularityStage
  ∷ singularityContradictionStage
  ∷ bkmGuardStage
  ∷ clayPromotionGuardStage
  ∷ []

a9StageCount : Nat
a9StageCount = listLength canonicalA9Stages

a9StageCountIs7 : a9StageCount ≡ 7
a9StageCountIs7 = refl

data A9Blocker : Set where
  actualPDEDecayToZeroMissing : A9Blocker
  vorticityVanishingTheoremMissing : A9Blocker
  ellipticRegularityBridgeMissing : A9Blocker
  cknBkmContradictionStillOpen : A9Blocker

canonicalA9Blockers : List A9Blocker
canonicalA9Blockers =
  actualPDEDecayToZeroMissing
  ∷ vorticityVanishingTheoremMissing
  ∷ ellipticRegularityBridgeMissing
  ∷ cknBkmContradictionStillOpen
  ∷ []

data NSA9SingularityContradictionRouteBoundary : Set where
  mkNSA9SingularityContradictionRouteBoundary :
    NSA9SingularityContradictionRouteBoundary

canonicalNSA9SingularityContradictionRouteBoundary :
  NSA9SingularityContradictionRouteBoundary
canonicalNSA9SingularityContradictionRouteBoundary =
  mkNSA9SingularityContradictionRouteBoundary

boundaryRecorded :
  NSA9SingularityContradictionRouteBoundary → Bool
boundaryRecorded _ = true

routeText :
  NSA9SingularityContradictionRouteBoundary → String
routeText _ =
  "A8 decay -> vorticity vanishing -> harmonicity/Biot-Savart -> elliptic regularity -> contradiction"

bkmCompatibilityRecorded :
  NSA9SingularityContradictionRouteBoundary → Bool
bkmCompatibilityRecorded _ = true

a9Proved :
  NSA9SingularityContradictionRouteBoundary → Bool
a9Proved _ = false

nsClayPromoted :
  NSA9SingularityContradictionRouteBoundary → Bool
nsClayPromoted _ = false

terminalPromotion :
  NSA9SingularityContradictionRouteBoundary → Bool
terminalPromotion _ = false

boundaryRecordedTrue :
  boundaryRecorded canonicalNSA9SingularityContradictionRouteBoundary ≡ true
boundaryRecordedTrue = refl

bkmCompatibilityRecordedTrue :
  bkmCompatibilityRecorded canonicalNSA9SingularityContradictionRouteBoundary
  ≡ true
bkmCompatibilityRecordedTrue = refl

a9StillOpen :
  a9Proved canonicalNSA9SingularityContradictionRouteBoundary ≡ false
a9StillOpen = refl

nsClayStillFalse :
  nsClayPromoted canonicalNSA9SingularityContradictionRouteBoundary ≡ false
nsClayStillFalse = refl

