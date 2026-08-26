module DASHI.Cognition.PNF.PackedOperatorFamilyAdmissionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Generic A2 family admission.  Normative, condition, exception and
-- transition are instances of one admission/solve boundary, not four
-- semantic authorities.  The implementation may fuse the cheap scan while
-- retaining independent exposed-family work receipts.
------------------------------------------------------------------------

data OperatorFamily : Set where
  normative condition exception transition : OperatorFamily

data FamilyAdmission : Set where
  rejected admitted : FamilyAdmission

record PackedOperatorFamilyArchitecture (Input Delta : Set) : Set₁ where
  field
    admission : OperatorFamily → Input → FamilyAdmission
    emptyDelta : OperatorFamily → Delta
    solve : OperatorFamily → Input → Delta
    reference : OperatorFamily → Input → Delta

    rejectedExact :
      (family : OperatorFamily) (input : Input) →
      admission family input ≡ rejected →
      reference family input ≡ emptyDelta family

    admittedExact :
      (family : OperatorFamily) (input : Input) →
      admission family input ≡ admitted →
      solve family input ≡ reference family input

open PackedOperatorFamilyArchitecture public

familyAdmissionIsExact :
  ∀ {Input Delta : Set}
    (architecture : PackedOperatorFamilyArchitecture Input Delta)
    (family : OperatorFamily) (input : Input) →
    admission architecture family input ≡ rejected →
    reference architecture family input ≡ emptyDelta architecture family
familyAdmissionIsExact architecture family input witness =
  rejectedExact architecture family input witness

familySolveIsReference :
  ∀ {Input Delta : Set}
    (architecture : PackedOperatorFamilyArchitecture Input Delta)
    (family : OperatorFamily) (input : Input) →
    admission architecture family input ≡ admitted →
    solve architecture family input ≡ reference architecture family input
familySolveIsReference architecture family input witness =
  admittedExact architecture family input witness

------------------------------------------------------------------------
-- Fused receipt: one cheap scan across N fibres, then E-wide work per family.
------------------------------------------------------------------------

record PackedOperatorFamilyWorkReceipt : Set where
  constructor packedOperatorFamilyWorkReceipt
  field
    inputFibreCount : Nat
    packedScanCount : Nat
    topologyBuildCount : Nat
    admittedFibreCount : Nat
    familyAdmittedCount : OperatorFamily → Nat
    familySolveCount : OperatorFamily → Nat

    oneAdmissionPerFibre : packedScanCount ≡ inputFibreCount
    topologyOnlyForAdmitted : topologyBuildCount ≡ admittedFibreCount
    familySolveMatchesExposure :
      (family : OperatorFamily) →
      familySolveCount family ≡ familyAdmittedCount family

open PackedOperatorFamilyWorkReceipt public

------------------------------------------------------------------------
-- Admission is not deletion, and family technology does not earn semantic
-- privilege merely by being packed or fused.
------------------------------------------------------------------------

data RejectedFamilyRequiresTopology : Set where
data RejectedFamilyDeletesParserEvidence : Set where
data FusedFamilyAdmissionCreatesAuthority : Set where

rejectedFamilyNeedNotBuildTopology : RejectedFamilyRequiresTopology → ⊥
rejectedFamilyNeedNotBuildTopology ()

rejectedFamilyDoesNotDeleteEvidence :
  RejectedFamilyDeletesParserEvidence → ⊥
rejectedFamilyDoesNotDeleteEvidence ()

fusedAdmissionDoesNotCreateAuthority :
  FusedFamilyAdmissionCreatesAuthority → ⊥
fusedAdmissionDoesNotCreateAuthority ()
