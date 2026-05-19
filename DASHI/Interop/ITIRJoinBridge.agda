module DASHI.Interop.ITIRJoinBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; _⊔_)

open import DASHI.Pressure as P using (Pressure; _⊑p_; _⊔p_)
open import UFTC_Lattice as UFTC using (Severity; Code)

------------------------------------------------------------------------
-- Conservative adapter from the ITIR/UFTC join lattice into DASHI pressure.
--
-- This is an adapter surface only. It does not import a live ITIR runtime,
-- does not classify real join edges, and does not promote the doc-only
-- JoinEdgePressureBridge into an aggregate DASHI theorem.

severityToPressure : Severity → Pressure
severityToPressure = P.fromLevel

codeToPressure : Code → Pressure
codeToPressure c = severityToPressure (UFTC.severity c)

severityJoinPreserved :
  ∀ a b →
  severityToPressure (a UFTC.⊔s b)
  ≡
  severityToPressure a ⊔p severityToPressure b
severityJoinPreserved zero zero = refl
severityJoinPreserved zero (suc zero) = refl
severityJoinPreserved zero (suc (suc zero)) = refl
severityJoinPreserved zero (suc (suc (suc zero))) = refl
severityJoinPreserved zero (suc (suc (suc (suc b)))) = refl
severityJoinPreserved (suc zero) zero = refl
severityJoinPreserved (suc zero) (suc zero) = refl
severityJoinPreserved (suc zero) (suc (suc zero)) = refl
severityJoinPreserved (suc zero) (suc (suc (suc zero))) = refl
severityJoinPreserved (suc zero) (suc (suc (suc (suc b)))) = refl
severityJoinPreserved (suc (suc zero)) zero = refl
severityJoinPreserved (suc (suc zero)) (suc zero) = refl
severityJoinPreserved (suc (suc zero)) (suc (suc zero)) = refl
severityJoinPreserved (suc (suc zero)) (suc (suc (suc zero))) = refl
severityJoinPreserved (suc (suc zero)) (suc (suc (suc (suc b)))) = refl
severityJoinPreserved (suc (suc (suc zero))) zero = refl
severityJoinPreserved (suc (suc (suc zero))) (suc zero) = refl
severityJoinPreserved (suc (suc (suc zero))) (suc (suc zero)) = refl
severityJoinPreserved (suc (suc (suc zero))) (suc (suc (suc zero))) = refl
severityJoinPreserved (suc (suc (suc zero))) (suc (suc (suc (suc b)))) = refl
severityJoinPreserved (suc (suc (suc (suc a)))) zero = refl
severityJoinPreserved (suc (suc (suc (suc a)))) (suc zero) = refl
severityJoinPreserved (suc (suc (suc (suc a)))) (suc (suc zero)) = refl
severityJoinPreserved (suc (suc (suc (suc a)))) (suc (suc (suc zero))) = refl
severityJoinPreserved (suc (suc (suc (suc a)))) (suc (suc (suc (suc b)))) = refl

codeXorJoinPreserved :
  ∀ x y →
  codeToPressure (UFTC.C_XOR x y)
  ≡
  codeToPressure x ⊔p codeToPressure y
codeXorJoinPreserved x y =
  severityJoinPreserved (UFTC.severity x) (UFTC.severity y)

SeverityToPressureMonotoneGap : Set
SeverityToPressureMonotoneGap =
  ∀ {a b} →
  a UFTC.⊑ b →
  severityToPressure a ⊑p severityToPressure b

CodeToPressureMonotoneGap : Set
CodeToPressureMonotoneGap =
  ∀ {x y} →
  UFTC.severity x UFTC.⊑ UFTC.severity y →
  codeToPressure x ⊑p codeToPressure y

record ITIRJoinBridgeObligations : Set₁ where
  field
    severityJoinPreservation :
      ∀ a b →
      severityToPressure (a UFTC.⊔s b)
      ≡
      severityToPressure a ⊔p severityToPressure b

    codeXorJoinPreservation :
      ∀ x y →
      codeToPressure (UFTC.C_XOR x y)
      ≡
      codeToPressure x ⊔p codeToPressure y

    severityMonotonicityGap : Set
    codeMonotonicityGap : Set

    nonClaimBoundary : List String

itirJoinBridgeObligations : ITIRJoinBridgeObligations
itirJoinBridgeObligations =
  record
    { severityJoinPreservation = severityJoinPreserved
    ; codeXorJoinPreservation = codeXorJoinPreserved
    ; severityMonotonicityGap = SeverityToPressureMonotoneGap
    ; codeMonotonicityGap = CodeToPressureMonotoneGap
    ; nonClaimBoundary =
        "ITIRJoinBridge is only a conservative UFTC severity/code to DASHI pressure adapter"
        ∷ "It proves finite saturation join preservation for severityToPressure and codeToPressure over C_XOR"
        ∷ "It does not import a live ITIR runtime, classify production join edges, or promote Docs/JoinEdgePressureBridge.md into a system theorem"
        ∷ "Full monotonicity is exposed as named proof-gap types rather than asserted"
        ∷ []
    }
