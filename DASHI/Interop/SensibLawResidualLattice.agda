module DASHI.Interop.SensibLawResidualLattice where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Properties as NatP using (m≤m⊔n; m≤n⊔m; ⊔-assoc; ⊔-comm; ⊔-idem; ⊔-lub)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)

open import Base369 using (HexTruth; hex-0; hex-1; hex-2; hex-3; hex-4; hex-5; rotateHex)
open import DASHI.Pressure as P using (Pressure; _⊔p_)
open import DASHI.Interop.ITIRJoinBridge as ITIR
open import UFTC_Lattice as UFTC using (Severity; _⊑_; _⊔s_)

------------------------------------------------------------------------
-- SensibLaw residual lattice, formalized as a bounded DASHI-side carrier.
--
-- This module mirrors the runtime SensibLaw residual levels as an Agda
-- four-chain.  It does not parse text, import spaCy, infer semantics, or
-- decide Wikidata / routing authority.

data ResidualLevel : Set where
  exact : ResidualLevel
  partial : ResidualLevel
  noTypedMeet : ResidualLevel
  contradiction : ResidualLevel

residualSeverity : ResidualLevel → Severity
residualSeverity exact = zero
residualSeverity partial = suc zero
residualSeverity noTypedMeet = suc (suc (suc zero))
residualSeverity contradiction =
  suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

_⊑r_ : ResidualLevel → ResidualLevel → Set
a ⊑r b = residualSeverity a ⊑ residualSeverity b

residualToPressure : ResidualLevel → Pressure
residualToPressure r = ITIR.severityToPressure (residualSeverity r)

joinResidual : ResidualLevel → ResidualLevel → ResidualLevel
joinResidual exact b = b
joinResidual partial exact = partial
joinResidual partial partial = partial
joinResidual partial noTypedMeet = noTypedMeet
joinResidual partial contradiction = contradiction
joinResidual noTypedMeet exact = noTypedMeet
joinResidual noTypedMeet partial = noTypedMeet
joinResidual noTypedMeet noTypedMeet = noTypedMeet
joinResidual noTypedMeet contradiction = contradiction
joinResidual contradiction b = contradiction

residualSeverity-injective :
  ∀ {a b} →
  residualSeverity a ≡ residualSeverity b →
  a ≡ b
residualSeverity-injective {exact} {exact} _ = refl
residualSeverity-injective {exact} {partial} ()
residualSeverity-injective {exact} {noTypedMeet} ()
residualSeverity-injective {exact} {contradiction} ()
residualSeverity-injective {partial} {exact} ()
residualSeverity-injective {partial} {partial} _ = refl
residualSeverity-injective {partial} {noTypedMeet} ()
residualSeverity-injective {partial} {contradiction} ()
residualSeverity-injective {noTypedMeet} {exact} ()
residualSeverity-injective {noTypedMeet} {partial} ()
residualSeverity-injective {noTypedMeet} {noTypedMeet} _ = refl
residualSeverity-injective {noTypedMeet} {contradiction} ()
residualSeverity-injective {contradiction} {exact} ()
residualSeverity-injective {contradiction} {partial} ()
residualSeverity-injective {contradiction} {noTypedMeet} ()
residualSeverity-injective {contradiction} {contradiction} _ = refl

residualJoinSeverity :
  ∀ a b →
  residualSeverity (joinResidual a b)
  ≡ residualSeverity a ⊔s residualSeverity b
residualJoinSeverity exact exact = refl
residualJoinSeverity exact partial = refl
residualJoinSeverity exact noTypedMeet = refl
residualJoinSeverity exact contradiction = refl
residualJoinSeverity partial exact = refl
residualJoinSeverity partial partial = refl
residualJoinSeverity partial noTypedMeet = refl
residualJoinSeverity partial contradiction = refl
residualJoinSeverity noTypedMeet exact = refl
residualJoinSeverity noTypedMeet partial = refl
residualJoinSeverity noTypedMeet noTypedMeet = refl
residualJoinSeverity noTypedMeet contradiction = refl
residualJoinSeverity contradiction exact = refl
residualJoinSeverity contradiction partial = refl
residualJoinSeverity contradiction noTypedMeet = refl
residualJoinSeverity contradiction contradiction = refl

joinResidual-idem : ∀ a → joinResidual a a ≡ a
joinResidual-idem a =
  residualSeverity-injective
    (trans
      (residualJoinSeverity a a)
      (⊔-idem (residualSeverity a)))

joinResidual-comm :
  ∀ a b →
  joinResidual a b ≡ joinResidual b a
joinResidual-comm a b =
  residualSeverity-injective
    (trans
      (residualJoinSeverity a b)
      (trans
        (⊔-comm (residualSeverity a) (residualSeverity b))
        (sym (residualJoinSeverity b a))))

joinResidual-assoc :
  ∀ a b c →
  joinResidual (joinResidual a b) c
  ≡
  joinResidual a (joinResidual b c)
joinResidual-assoc a b c =
  residualSeverity-injective
    (trans
      (residualJoinSeverity (joinResidual a b) c)
      (trans
        (cong (_⊔s residualSeverity c) (residualJoinSeverity a b))
        (trans
          (⊔-assoc (residualSeverity a) (residualSeverity b) (residualSeverity c))
          (trans
            (sym (cong (residualSeverity a ⊔s_) (residualJoinSeverity b c)))
            (sym (residualJoinSeverity a (joinResidual b c)))))))

joinResidual-upper-left :
  ∀ a b →
  a ⊑r joinResidual a b
joinResidual-upper-left a b rewrite residualJoinSeverity a b =
  m≤m⊔n (residualSeverity a) (residualSeverity b)

joinResidual-upper-right :
  ∀ a b →
  b ⊑r joinResidual a b
joinResidual-upper-right a b rewrite residualJoinSeverity a b =
  m≤n⊔m (residualSeverity a) (residualSeverity b)

joinResidual-least :
  ∀ {a b c} →
  a ⊑r c →
  b ⊑r c →
  joinResidual a b ⊑r c
joinResidual-least {a} {b} {c} a≤c b≤c
  rewrite residualJoinSeverity a b =
    ⊔-lub a≤c b≤c

residualPressureJoinPreserved :
  ∀ a b →
  residualToPressure (joinResidual a b)
  ≡
  residualToPressure a ⊔p residualToPressure b
residualPressureJoinPreserved a b =
  trans
    (cong ITIR.severityToPressure (residualJoinSeverity a b))
    (ITIR.severityJoinPreserved (residualSeverity a) (residualSeverity b))

------------------------------------------------------------------------
-- Minimal PredicatePNF carrier.
--
-- This records the type shape needed to discuss a PNF atom in Agda.  It is not
-- a parser and does not claim that runtime text produced any such value.

data StructuralSignature : Set where
  sig-agent-theme : StructuralSignature
  sig-agent-goal : StructuralSignature
  sig-theme-only : StructuralSignature
  sig-unclassified : StructuralSignature

data TypedArg : Set where
  absent : TypedArg
  opaqueArg : String → TypedArg

data QualifierState : Set where
  positive : QualifierState
  negated : QualifierState
  modal : QualifierState
  qualifierUnknown : QualifierState

data WrapperState : Set where
  directEvidence : WrapperState
  hedgedEvidence : WrapperState
  attributedEvidence : WrapperState
  performativeEvidence : WrapperState
  wrapperUnknown : WrapperState

record PredicatePNF : Set where
  constructor predicatePNF
  field
    predicate : String
    structuralSignature : StructuralSignature
    agent : TypedArg
    theme : TypedArg
    goal : TypedArg
    qualifier : QualifierState
    wrapper : WrapperState
    provenance : String

record PNFEmissionReceipt : Set where
  constructor pnfEmissionReceipt
  field
    parserProfile : String
    reducerProfile : String
    sourceSpan : String
    emittedAtom : PredicatePNF

------------------------------------------------------------------------
-- Fibred PNF comparison surface.
--
-- The residual chain is only directly meaningful inside one structural
-- signature fibre. Cross-signature comparison cannot reach exact/partial and
-- collapses to noTypedMeet. Wrapper mismatch is an additional gate that keeps
-- hedged/attributed/unknown evidence from being treated as exact.

sameStructuralSignature : StructuralSignature → StructuralSignature → Bool
sameStructuralSignature sig-agent-theme sig-agent-theme = true
sameStructuralSignature sig-agent-theme sig-agent-goal = false
sameStructuralSignature sig-agent-theme sig-theme-only = false
sameStructuralSignature sig-agent-theme sig-unclassified = false
sameStructuralSignature sig-agent-goal sig-agent-theme = false
sameStructuralSignature sig-agent-goal sig-agent-goal = true
sameStructuralSignature sig-agent-goal sig-theme-only = false
sameStructuralSignature sig-agent-goal sig-unclassified = false
sameStructuralSignature sig-theme-only sig-agent-theme = false
sameStructuralSignature sig-theme-only sig-agent-goal = false
sameStructuralSignature sig-theme-only sig-theme-only = true
sameStructuralSignature sig-theme-only sig-unclassified = false
sameStructuralSignature sig-unclassified sig-agent-theme = false
sameStructuralSignature sig-unclassified sig-agent-goal = false
sameStructuralSignature sig-unclassified sig-theme-only = false
sameStructuralSignature sig-unclassified sig-unclassified = true

sameWrapper : WrapperState → WrapperState → Bool
sameWrapper directEvidence directEvidence = true
sameWrapper directEvidence hedgedEvidence = false
sameWrapper directEvidence attributedEvidence = false
sameWrapper directEvidence performativeEvidence = false
sameWrapper directEvidence wrapperUnknown = false
sameWrapper hedgedEvidence directEvidence = false
sameWrapper hedgedEvidence hedgedEvidence = true
sameWrapper hedgedEvidence attributedEvidence = false
sameWrapper hedgedEvidence performativeEvidence = false
sameWrapper hedgedEvidence wrapperUnknown = false
sameWrapper attributedEvidence directEvidence = false
sameWrapper attributedEvidence hedgedEvidence = false
sameWrapper attributedEvidence attributedEvidence = true
sameWrapper attributedEvidence performativeEvidence = false
sameWrapper attributedEvidence wrapperUnknown = false
sameWrapper performativeEvidence directEvidence = false
sameWrapper performativeEvidence hedgedEvidence = false
sameWrapper performativeEvidence attributedEvidence = false
sameWrapper performativeEvidence performativeEvidence = true
sameWrapper performativeEvidence wrapperUnknown = false
sameWrapper wrapperUnknown directEvidence = false
sameWrapper wrapperUnknown hedgedEvidence = false
sameWrapper wrapperUnknown attributedEvidence = false
sameWrapper wrapperUnknown performativeEvidence = false
sameWrapper wrapperUnknown wrapperUnknown = true

sameQualifier : QualifierState → QualifierState → Bool
sameQualifier positive positive = true
sameQualifier positive negated = false
sameQualifier positive modal = false
sameQualifier positive qualifierUnknown = false
sameQualifier negated positive = false
sameQualifier negated negated = true
sameQualifier negated modal = false
sameQualifier negated qualifierUnknown = false
sameQualifier modal positive = false
sameQualifier modal negated = false
sameQualifier modal modal = true
sameQualifier modal qualifierUnknown = false
sameQualifier qualifierUnknown positive = false
sameQualifier qualifierUnknown negated = false
sameQualifier qualifierUnknown modal = false
sameQualifier qualifierUnknown qualifierUnknown = true

sameTypedArg : TypedArg → TypedArg → Bool
sameTypedArg absent absent = true
sameTypedArg absent (opaqueArg _) = false
sameTypedArg (opaqueArg _) absent = false
sameTypedArg (opaqueArg _) (opaqueArg _) = true

roleOverlap : PredicatePNF → PredicatePNF → Bool
roleOverlap a b with
  sameTypedArg (PredicatePNF.agent a) (PredicatePNF.agent b) |
  sameTypedArg (PredicatePNF.theme a) (PredicatePNF.theme b) |
  sameTypedArg (PredicatePNF.goal a) (PredicatePNF.goal b)
... | true | _ | _ = true
... | false | true | _ = true
... | false | false | true = true
... | false | false | false = false

data SignatureComparison : Set where
  sameSignature : SignatureComparison
  differentSignature : SignatureComparison

signatureComparison : PredicatePNF → PredicatePNF → SignatureComparison
signatureComparison a b with
  sameStructuralSignature
    (PredicatePNF.structuralSignature a)
    (PredicatePNF.structuralSignature b)
... | true = sameSignature
... | false = differentSignature

data WrapperComparison : Set where
  wrapperLicensed : WrapperComparison
  wrapperFiltered : WrapperComparison

wrapperComparison : PredicatePNF → PredicatePNF → WrapperComparison
wrapperComparison a b with sameWrapper (PredicatePNF.wrapper a) (PredicatePNF.wrapper b)
... | true = wrapperLicensed
... | false = wrapperFiltered

compareWithinSignature : PredicatePNF → PredicatePNF → ResidualLevel
compareWithinSignature a b with wrapperComparison a b
... | wrapperFiltered = partial
... | wrapperLicensed with sameQualifier (PredicatePNF.qualifier a) (PredicatePNF.qualifier b)
...   | false = contradiction
...   | true with roleOverlap a b
...     | true = exact
...     | false = partial

computeResidual : PredicatePNF → PredicatePNF → ResidualLevel
computeResidual a b with signatureComparison a b
... | differentSignature = noTypedMeet
... | sameSignature = compareWithinSignature a b

receiptResidual : PNFEmissionReceipt → PNFEmissionReceipt → ResidualLevel
receiptResidual a b =
  computeResidual
    (PNFEmissionReceipt.emittedAtom a)
    (PNFEmissionReceipt.emittedAtom b)

crossSignature-noTypedMeet :
  ∀ a b →
  signatureComparison a b ≡ differentSignature →
  computeResidual a b ≡ noTypedMeet
crossSignature-noTypedMeet a b sig≡ rewrite sig≡ = refl

wrapperMismatch-notExact :
  ∀ a b →
  signatureComparison a b ≡ sameSignature →
  wrapperComparison a b ≡ wrapperFiltered →
  computeResidual a b ≡ partial
wrapperMismatch-notExact a b sig≡ wrap≡ rewrite sig≡ | wrap≡ = refl

data CandidateRef : Set where
  pnf-ref : Nat → CandidateRef
  pnf-fallback : CandidateRef

record PredicateIndexSurface : Set where
  constructor predicateIndexSurface
  field
    shortlistedBySignature : StructuralSignature → List CandidateRef
    fallbackRef : CandidateRef
    fallbackStable : fallbackRef ≡ pnf-fallback

defaultPredicateIndexSurface : PredicateIndexSurface
defaultPredicateIndexSurface =
  predicateIndexSurface
    (λ _ → pnf-fallback ∷ [])
    pnf-fallback
    refl

------------------------------------------------------------------------
-- Six-level residual carrier for the syad-style / HexTruth bridge.
--
-- This refines the four-level chain with underdetermined and scope-exceeded
-- states. It is separate from runtime SensibLaw unless that runtime adds the
-- corresponding levels and emits receipt evidence.

data SixResidualLevel : Set where
  exact6 : SixResidualLevel
  partial6 : SixResidualLevel
  underdetermined6 : SixResidualLevel
  noTypedMeet6 : SixResidualLevel
  scopeExceeded6 : SixResidualLevel
  contradiction6 : SixResidualLevel

sixResidualSeverity : SixResidualLevel → Severity
sixResidualSeverity exact6 = zero
sixResidualSeverity partial6 = suc zero
sixResidualSeverity underdetermined6 = suc (suc zero)
sixResidualSeverity noTypedMeet6 = suc (suc (suc zero))
sixResidualSeverity scopeExceeded6 = suc (suc (suc (suc zero)))
sixResidualSeverity contradiction6 =
  suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

sixResidualToPressure : SixResidualLevel → Pressure
sixResidualToPressure r = ITIR.severityToPressure (sixResidualSeverity r)

joinSixResidual : SixResidualLevel → SixResidualLevel → SixResidualLevel
joinSixResidual exact6 b = b
joinSixResidual partial6 exact6 = partial6
joinSixResidual partial6 partial6 = partial6
joinSixResidual partial6 underdetermined6 = underdetermined6
joinSixResidual partial6 noTypedMeet6 = noTypedMeet6
joinSixResidual partial6 scopeExceeded6 = scopeExceeded6
joinSixResidual partial6 contradiction6 = contradiction6
joinSixResidual underdetermined6 exact6 = underdetermined6
joinSixResidual underdetermined6 partial6 = underdetermined6
joinSixResidual underdetermined6 underdetermined6 = underdetermined6
joinSixResidual underdetermined6 noTypedMeet6 = noTypedMeet6
joinSixResidual underdetermined6 scopeExceeded6 = scopeExceeded6
joinSixResidual underdetermined6 contradiction6 = contradiction6
joinSixResidual noTypedMeet6 exact6 = noTypedMeet6
joinSixResidual noTypedMeet6 partial6 = noTypedMeet6
joinSixResidual noTypedMeet6 underdetermined6 = noTypedMeet6
joinSixResidual noTypedMeet6 noTypedMeet6 = noTypedMeet6
joinSixResidual noTypedMeet6 scopeExceeded6 = scopeExceeded6
joinSixResidual noTypedMeet6 contradiction6 = contradiction6
joinSixResidual scopeExceeded6 exact6 = scopeExceeded6
joinSixResidual scopeExceeded6 partial6 = scopeExceeded6
joinSixResidual scopeExceeded6 underdetermined6 = scopeExceeded6
joinSixResidual scopeExceeded6 noTypedMeet6 = scopeExceeded6
joinSixResidual scopeExceeded6 scopeExceeded6 = scopeExceeded6
joinSixResidual scopeExceeded6 contradiction6 = contradiction6
joinSixResidual contradiction6 b = contradiction6

sixResidualSeverity-injective :
  ∀ {a b} →
  sixResidualSeverity a ≡ sixResidualSeverity b →
  a ≡ b
sixResidualSeverity-injective {exact6} {exact6} _ = refl
sixResidualSeverity-injective {exact6} {partial6} ()
sixResidualSeverity-injective {exact6} {underdetermined6} ()
sixResidualSeverity-injective {exact6} {noTypedMeet6} ()
sixResidualSeverity-injective {exact6} {scopeExceeded6} ()
sixResidualSeverity-injective {exact6} {contradiction6} ()
sixResidualSeverity-injective {partial6} {exact6} ()
sixResidualSeverity-injective {partial6} {partial6} _ = refl
sixResidualSeverity-injective {partial6} {underdetermined6} ()
sixResidualSeverity-injective {partial6} {noTypedMeet6} ()
sixResidualSeverity-injective {partial6} {scopeExceeded6} ()
sixResidualSeverity-injective {partial6} {contradiction6} ()
sixResidualSeverity-injective {underdetermined6} {exact6} ()
sixResidualSeverity-injective {underdetermined6} {partial6} ()
sixResidualSeverity-injective {underdetermined6} {underdetermined6} _ = refl
sixResidualSeverity-injective {underdetermined6} {noTypedMeet6} ()
sixResidualSeverity-injective {underdetermined6} {scopeExceeded6} ()
sixResidualSeverity-injective {underdetermined6} {contradiction6} ()
sixResidualSeverity-injective {noTypedMeet6} {exact6} ()
sixResidualSeverity-injective {noTypedMeet6} {partial6} ()
sixResidualSeverity-injective {noTypedMeet6} {underdetermined6} ()
sixResidualSeverity-injective {noTypedMeet6} {noTypedMeet6} _ = refl
sixResidualSeverity-injective {noTypedMeet6} {scopeExceeded6} ()
sixResidualSeverity-injective {noTypedMeet6} {contradiction6} ()
sixResidualSeverity-injective {scopeExceeded6} {exact6} ()
sixResidualSeverity-injective {scopeExceeded6} {partial6} ()
sixResidualSeverity-injective {scopeExceeded6} {underdetermined6} ()
sixResidualSeverity-injective {scopeExceeded6} {noTypedMeet6} ()
sixResidualSeverity-injective {scopeExceeded6} {scopeExceeded6} _ = refl
sixResidualSeverity-injective {scopeExceeded6} {contradiction6} ()
sixResidualSeverity-injective {contradiction6} {exact6} ()
sixResidualSeverity-injective {contradiction6} {partial6} ()
sixResidualSeverity-injective {contradiction6} {underdetermined6} ()
sixResidualSeverity-injective {contradiction6} {noTypedMeet6} ()
sixResidualSeverity-injective {contradiction6} {scopeExceeded6} ()
sixResidualSeverity-injective {contradiction6} {contradiction6} _ = refl

sixResidualJoinSeverity :
  ∀ a b →
  sixResidualSeverity (joinSixResidual a b)
  ≡ sixResidualSeverity a ⊔s sixResidualSeverity b
sixResidualJoinSeverity exact6 exact6 = refl
sixResidualJoinSeverity exact6 partial6 = refl
sixResidualJoinSeverity exact6 underdetermined6 = refl
sixResidualJoinSeverity exact6 noTypedMeet6 = refl
sixResidualJoinSeverity exact6 scopeExceeded6 = refl
sixResidualJoinSeverity exact6 contradiction6 = refl
sixResidualJoinSeverity partial6 exact6 = refl
sixResidualJoinSeverity partial6 partial6 = refl
sixResidualJoinSeverity partial6 underdetermined6 = refl
sixResidualJoinSeverity partial6 noTypedMeet6 = refl
sixResidualJoinSeverity partial6 scopeExceeded6 = refl
sixResidualJoinSeverity partial6 contradiction6 = refl
sixResidualJoinSeverity underdetermined6 exact6 = refl
sixResidualJoinSeverity underdetermined6 partial6 = refl
sixResidualJoinSeverity underdetermined6 underdetermined6 = refl
sixResidualJoinSeverity underdetermined6 noTypedMeet6 = refl
sixResidualJoinSeverity underdetermined6 scopeExceeded6 = refl
sixResidualJoinSeverity underdetermined6 contradiction6 = refl
sixResidualJoinSeverity noTypedMeet6 exact6 = refl
sixResidualJoinSeverity noTypedMeet6 partial6 = refl
sixResidualJoinSeverity noTypedMeet6 underdetermined6 = refl
sixResidualJoinSeverity noTypedMeet6 noTypedMeet6 = refl
sixResidualJoinSeverity noTypedMeet6 scopeExceeded6 = refl
sixResidualJoinSeverity noTypedMeet6 contradiction6 = refl
sixResidualJoinSeverity scopeExceeded6 exact6 = refl
sixResidualJoinSeverity scopeExceeded6 partial6 = refl
sixResidualJoinSeverity scopeExceeded6 underdetermined6 = refl
sixResidualJoinSeverity scopeExceeded6 noTypedMeet6 = refl
sixResidualJoinSeverity scopeExceeded6 scopeExceeded6 = refl
sixResidualJoinSeverity scopeExceeded6 contradiction6 = refl
sixResidualJoinSeverity contradiction6 exact6 = refl
sixResidualJoinSeverity contradiction6 partial6 = refl
sixResidualJoinSeverity contradiction6 underdetermined6 = refl
sixResidualJoinSeverity contradiction6 noTypedMeet6 = refl
sixResidualJoinSeverity contradiction6 scopeExceeded6 = refl
sixResidualJoinSeverity contradiction6 contradiction6 = refl

joinSixResidual-idem : ∀ a → joinSixResidual a a ≡ a
joinSixResidual-idem a =
  sixResidualSeverity-injective
    (trans
      (sixResidualJoinSeverity a a)
      (⊔-idem (sixResidualSeverity a)))

joinSixResidual-comm :
  ∀ a b →
  joinSixResidual a b ≡ joinSixResidual b a
joinSixResidual-comm a b =
  sixResidualSeverity-injective
    (trans
      (sixResidualJoinSeverity a b)
      (trans
        (⊔-comm (sixResidualSeverity a) (sixResidualSeverity b))
        (sym (sixResidualJoinSeverity b a))))

joinSixResidual-assoc :
  ∀ a b c →
  joinSixResidual (joinSixResidual a b) c
  ≡
  joinSixResidual a (joinSixResidual b c)
joinSixResidual-assoc a b c =
  sixResidualSeverity-injective
    (trans
      (sixResidualJoinSeverity (joinSixResidual a b) c)
      (trans
        (cong (_⊔s sixResidualSeverity c) (sixResidualJoinSeverity a b))
        (trans
          (⊔-assoc (sixResidualSeverity a) (sixResidualSeverity b) (sixResidualSeverity c))
          (trans
            (sym (cong (sixResidualSeverity a ⊔s_) (sixResidualJoinSeverity b c)))
            (sym (sixResidualJoinSeverity a (joinSixResidual b c)))))))

sixResidualPressureJoinPreserved :
  ∀ a b →
  sixResidualToPressure (joinSixResidual a b)
  ≡
  sixResidualToPressure a ⊔p sixResidualToPressure b
sixResidualPressureJoinPreserved a b =
  trans
    (cong ITIR.severityToPressure (sixResidualJoinSeverity a b))
    (ITIR.severityJoinPreserved (sixResidualSeverity a) (sixResidualSeverity b))

hexToSixResidual : HexTruth → SixResidualLevel
hexToSixResidual hex-0 = exact6
hexToSixResidual hex-1 = partial6
hexToSixResidual hex-2 = underdetermined6
hexToSixResidual hex-3 = noTypedMeet6
hexToSixResidual hex-4 = scopeExceeded6
hexToSixResidual hex-5 = contradiction6

hexSeverity : HexTruth → Severity
hexSeverity h = sixResidualSeverity (hexToSixResidual h)

hexToPressure : HexTruth → Pressure
hexToPressure h = sixResidualToPressure (hexToSixResidual h)

wrapperSixResidual : WrapperState → SixResidualLevel
wrapperSixResidual directEvidence = exact6
wrapperSixResidual hedgedEvidence = underdetermined6
wrapperSixResidual attributedEvidence = underdetermined6
wrapperSixResidual performativeEvidence = scopeExceeded6
wrapperSixResidual wrapperUnknown = scopeExceeded6

receiptWrapperSixResidual : PNFEmissionReceipt → SixResidualLevel
receiptWrapperSixResidual r =
  wrapperSixResidual
    (PredicatePNF.wrapper (PNFEmissionReceipt.emittedAtom r))

performativeWrapper-scopeExceeded :
  wrapperSixResidual performativeEvidence ≡ scopeExceeded6
performativeWrapper-scopeExceeded = refl

directVsPerformative-filtered :
  sameWrapper directEvidence performativeEvidence ≡ false
directVsPerformative-filtered = refl

performativeVsDirect-filtered :
  sameWrapper performativeEvidence directEvidence ≡ false
performativeVsDirect-filtered = refl

rotateHex-nonwrap-severity-0 :
  hexSeverity hex-0 ⊑ hexSeverity (rotateHex hex-0)
rotateHex-nonwrap-severity-0 =
  NatP.m≤m⊔n (hexSeverity hex-0) (hexSeverity (rotateHex hex-0))

rotateHex-nonwrap-severity-1 :
  hexSeverity hex-1 ⊑ hexSeverity (rotateHex hex-1)
rotateHex-nonwrap-severity-1 =
  NatP.m≤m⊔n (hexSeverity hex-1) (hexSeverity (rotateHex hex-1))

rotateHex-nonwrap-severity-2 :
  hexSeverity hex-2 ⊑ hexSeverity (rotateHex hex-2)
rotateHex-nonwrap-severity-2 =
  NatP.m≤m⊔n (hexSeverity hex-2) (hexSeverity (rotateHex hex-2))

rotateHex-nonwrap-severity-3 :
  hexSeverity hex-3 ⊑ hexSeverity (rotateHex hex-3)
rotateHex-nonwrap-severity-3 =
  NatP.m≤m⊔n (hexSeverity hex-3) (hexSeverity (rotateHex hex-3))

rotateHex-nonwrap-severity-4 :
  hexSeverity hex-4 ⊑ hexSeverity (rotateHex hex-4)
rotateHex-nonwrap-severity-4 =
  NatP.m≤m⊔n (hexSeverity hex-4) (hexSeverity (rotateHex hex-4))

rotateHexWrapSeam :
  hexSeverity (rotateHex hex-5) ≡ zero
rotateHexWrapSeam = refl

hexRotatePressureJoin :
  ∀ h →
  hexToPressure h ⊔p hexToPressure (rotateHex h)
  ≡
  ITIR.severityToPressure (hexSeverity h ⊔s hexSeverity (rotateHex h))
hexRotatePressureJoin h =
  sym (ITIR.severityJoinPreserved (hexSeverity h) (hexSeverity (rotateHex h)))

record SensibLawResidualBridgeSurface : Set₁ where
  field
    residualCarrier : Set
    pnfCarrier : Set
    receiptCarrier : Set
    join : ResidualLevel → ResidualLevel → ResidualLevel
    join-idem : ∀ a → join a a ≡ a
    join-comm : ∀ a b → join a b ≡ join b a
    join-assoc : ∀ a b c → join (join a b) c ≡ join a (join b c)
    pressureJoinPreserved :
      ∀ a b →
      residualToPressure (join a b)
      ≡
      residualToPressure a ⊔p residualToPressure b
    fibredCompare : PredicatePNF → PredicatePNF → ResidualLevel
    receiptCompare : PNFEmissionReceipt → PNFEmissionReceipt → ResidualLevel
    predicateIndexCarrier : Set
    sixResidualCarrier : Set
    hexEmbedding : HexTruth → SixResidualLevel
    wrapperSixResidualProjection : WrapperState → SixResidualLevel
    sixJoin-idem : ∀ a → joinSixResidual a a ≡ a
    sixJoin-comm : ∀ a b → joinSixResidual a b ≡ joinSixResidual b a
    sixJoin-assoc :
      ∀ a b c →
      joinSixResidual (joinSixResidual a b) c
      ≡
      joinSixResidual a (joinSixResidual b c)
    sixPressureJoinPreserved :
      ∀ a b →
      sixResidualToPressure (joinSixResidual a b)
      ≡
      sixResidualToPressure a ⊔p sixResidualToPressure b
    nonClaimBoundary : List String

sensibLawResidualBridgeSurface : SensibLawResidualBridgeSurface
sensibLawResidualBridgeSurface =
  record
    { residualCarrier = ResidualLevel
    ; pnfCarrier = PredicatePNF
    ; receiptCarrier = PNFEmissionReceipt
    ; join = joinResidual
    ; join-idem = joinResidual-idem
    ; join-comm = joinResidual-comm
    ; join-assoc = joinResidual-assoc
    ; pressureJoinPreserved = residualPressureJoinPreserved
    ; fibredCompare = computeResidual
    ; receiptCompare = receiptResidual
    ; predicateIndexCarrier = PredicateIndexSurface
    ; sixResidualCarrier = SixResidualLevel
    ; hexEmbedding = hexToSixResidual
    ; wrapperSixResidualProjection = wrapperSixResidual
    ; sixJoin-idem = joinSixResidual-idem
    ; sixJoin-comm = joinSixResidual-comm
    ; sixJoin-assoc = joinSixResidual-assoc
    ; sixPressureJoinPreserved = sixResidualPressureJoinPreserved
    ; nonClaimBoundary =
        "ResidualLevel is a DASHI-side four-chain mirror of the SensibLaw runtime residual ladder"
        ∷ "PredicatePNF is a typed carrier shape only, not a parser or semantic authority"
        ∷ "PNF comparison is fibred by StructuralSignature; cross-fibre comparison collapses to noTypedMeet"
        ∷ "WrapperState gates exactness before role/qualifier comparison"
        ∷ "Performative wrappers map to scopeExceeded6 unless a future receipt promotes them into evidence"
        ∷ "SixResidualLevel is a six-state DASHI refinement; runtime SensibLaw must emit receipts before it is operational"
        ∷ "spaCy token/dependency parses remain structural substrate and cannot produce theorem claims directly"
        ∷ "Residual joins map into UFTC severity and DASHI pressure; they do not decide Wikidata edits or routes"
        ∷ []
    }
