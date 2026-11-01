module DASHI.Physics.Closure.Validation.RealizationProfileRigidity where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import DASHI.Geometry.ConeTimeIsotropy as CTI

data ComparisonRole : Set where
  admissibleCandidate : ComparisonRole
  negativeControl : ComparisonRole

record RealizationObservation : Set where
  field
    role : ComparisonRole
    label : String
    orientationTag : Maybe Nat
    shell1Profile : List Nat
    shell2Profile : List Nat
    signature : Maybe CTI.Signature

record AdmissibleComparisonRealization : Set where
  field
    label : String
    orientationTag : Nat
    shell1Profile : List Nat
    shell2Profile : List Nat
    signature : CTI.Signature

toObservation :
  AdmissibleComparisonRealization → RealizationObservation
toObservation candidate =
  record
    { role = admissibleCandidate
    ; label = AdmissibleComparisonRealization.label candidate
    ; orientationTag = just (AdmissibleComparisonRealization.orientationTag candidate)
    ; shell1Profile = AdmissibleComparisonRealization.shell1Profile candidate
    ; shell2Profile = AdmissibleComparisonRealization.shell2Profile candidate
    ; signature = just (AdmissibleComparisonRealization.signature candidate)
    }

data RigidityVerdict : Set where
  exactMatch : RigidityVerdict
  signatureOnlyMatch : RigidityVerdict
  mismatch : RigidityVerdict

signatureEq : CTI.Signature → CTI.Signature → Bool
signatureEq CTI.sig31 CTI.sig31 = true
signatureEq CTI.sig13 CTI.sig13 = true
signatureEq CTI.other CTI.other = true
signatureEq _ _ = false

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

listNatEq : List Nat → List Nat → Bool
listNatEq [] [] = true
listNatEq [] (_ ∷ _) = false
listNatEq (_ ∷ _) [] = false
listNatEq (x ∷ xs) (y ∷ ys) with natEq x y
... | true = listNatEq xs ys
... | false = false

and : Bool → Bool → Bool
and true true = true
and _ _ = false

record MatchFacts (reference candidate : RealizationObservation) : Set where
  field
    orientationAvailable : Bool
    orientationMatches : Bool
    shell1Matches : Bool
    shell2Matches : Bool
    signatureAvailable : Bool
    signatureMatches : Bool

maybeNatMatches : Maybe Nat → Maybe Nat → Bool
maybeNatMatches (just x) (just y) = natEq x y
maybeNatMatches _ _ = false

maybeNatAvailable : Maybe Nat → Maybe Nat → Bool
maybeNatAvailable (just _) (just _) = true
maybeNatAvailable _ _ = false

maybeSignatureMatches : Maybe CTI.Signature → Maybe CTI.Signature → Bool
maybeSignatureMatches (just x) (just y) = signatureEq x y
maybeSignatureMatches _ _ = false

maybeSignatureAvailable : Maybe CTI.Signature → Maybe CTI.Signature → Bool
maybeSignatureAvailable (just _) (just _) = true
maybeSignatureAvailable _ _ = false

computeFacts :
  (reference candidate : RealizationObservation) → MatchFacts reference candidate
computeFacts reference candidate =
  record
    { orientationAvailable =
        maybeNatAvailable
          (RealizationObservation.orientationTag reference)
          (RealizationObservation.orientationTag candidate)
    ; orientationMatches =
        maybeNatMatches
          (RealizationObservation.orientationTag reference)
          (RealizationObservation.orientationTag candidate)
    ; shell1Matches =
        listNatEq
          (RealizationObservation.shell1Profile reference)
          (RealizationObservation.shell1Profile candidate)
    ; shell2Matches =
        listNatEq
          (RealizationObservation.shell2Profile reference)
          (RealizationObservation.shell2Profile candidate)
    ; signatureAvailable =
        maybeSignatureAvailable
          (RealizationObservation.signature reference)
          (RealizationObservation.signature candidate)
    ; signatureMatches =
        maybeSignatureMatches
          (RealizationObservation.signature reference)
          (RealizationObservation.signature candidate)
    }

classify : ∀ {reference candidate} → MatchFacts reference candidate → RigidityVerdict
classify facts with MatchFacts.signatureAvailable facts
... | false = mismatch
... | true with MatchFacts.signatureMatches facts
... | false = mismatch
... | true with and
  (MatchFacts.shell1Matches facts)
  (MatchFacts.shell2Matches facts)
... | false = signatureOnlyMatch
... | true with and
  (MatchFacts.orientationAvailable facts)
  (MatchFacts.orientationMatches facts)
... | true = exactMatch
... | false = signatureOnlyMatch
