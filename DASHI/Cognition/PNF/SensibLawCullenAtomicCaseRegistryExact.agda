module DASHI.Cognition.PNF.SensibLawCullenAtomicCaseRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact as CullenCLA
import DASHI.Cognition.PNF.SensibLawCullenS43ASpecialStatutoryPowerAtomicExact as S43A
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Vicarious
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilityActAtomicSourceAtlasExact as VicariousAct

cullenCaseContext : Ontology.StableId
cullenCaseContext = Ontology.stableId "case:Cullen:[2026]HCA19:retained-fibre"

------------------------------------------------------------------------
-- Entry is indexed by the exact legal proposition.  There is no lookup from an
-- untyped tag back into a proposition and therefore no proposition-identity seam.
------------------------------------------------------------------------

data CullenAtomicEntry : Algebra.LegalProposition → Set where
  s5BForeseeableEntry : CullenAtomicEntry CLA.riskForeseeable
  s5BNotInsignificantEntry : CullenAtomicEntry CLA.riskNotInsignificant
  s5BReasonablePrecautionsEntry : CullenAtomicEntry CLA.reasonablePersonWouldTakePrecautions
  s43AEngagementEntry : CullenAtomicEntry S43A.liabilityBasedOnExerciseOfSpecialStatutoryPower
  vicariousFamilyEntry : CullenAtomicEntry VicariousAct.crownVicariousLiabilityRecognised

cullenCanonicalTestFor :
  ∀ {p} → CullenAtomicEntry p →
  Atomic.SourceConditionedAtomicLegalTest p
cullenCanonicalTestFor s5BForeseeableEntry = CullenCLA.cullenForeseeableAtom
cullenCanonicalTestFor s5BNotInsignificantEntry = CullenCLA.cullenNotInsignificantAtom
cullenCanonicalTestFor s5BReasonablePrecautionsEntry = CullenCLA.cullenReasonablePrecautionsAtom
cullenCanonicalTestFor s43AEngagementEntry = S43A.cullenS43ABasedOnAtom
cullenCanonicalTestFor vicariousFamilyEntry = Vicarious.cullenVicariousFamilyAtom

cullenAtomicRegistry : Coherence.AtomicCaseRegistry
cullenAtomicRegistry = Coherence.atomic-case-registry
  CullenAtomicEntry
  (λ _ → cullenCaseContext)
  cullenCanonicalTestFor
  "Finite proposition-indexed Cullen atomic registry: joint-reasons s 5B outcomes, Edelman concurrence s 43A non-engagement, and source-conditioned vicarious-family recognition."

cullenRegisteredForeseeablePositive :
  Atomic.gate (Coherence.canonicalTestFor cullenAtomicRegistry s5BForeseeableEntry) ≡ BT.pos
cullenRegisteredForeseeablePositive = refl

cullenRegisteredNotInsignificantPositive :
  Atomic.gate (Coherence.canonicalTestFor cullenAtomicRegistry s5BNotInsignificantEntry) ≡ BT.pos
cullenRegisteredNotInsignificantPositive = refl

cullenRegisteredReasonablePrecautionsNegative :
  Atomic.gate (Coherence.canonicalTestFor cullenAtomicRegistry s5BReasonablePrecautionsEntry) ≡ BT.neg
cullenRegisteredReasonablePrecautionsNegative = refl

cullenRegisteredS43ANegative :
  Atomic.gate (Coherence.canonicalTestFor cullenAtomicRegistry s43AEngagementEntry) ≡ BT.neg
cullenRegisteredS43ANegative = refl

cullenRegisteredVicariousFamilyPositive :
  Atomic.gate (Coherence.canonicalTestFor cullenAtomicRegistry vicariousFamilyEntry) ≡ BT.pos
cullenRegisteredVicariousFamilyPositive = refl

------------------------------------------------------------------------
-- Non-bypass theorems.
------------------------------------------------------------------------

cullenBreachAtomCannotBeReintroducedPositive :
  (candidate :
    Coherence.RegisteredAtomicTest
      cullenAtomicRegistry s5BReasonablePrecautionsEntry) →
  Atomic.gate (Coherence.candidateTest candidate) ≡ BT.pos →
  ⊥
cullenBreachAtomCannotBeReintroducedPositive =
  Coherence.registeredNegativeCannotBeReintroducedPositive
    cullenRegisteredReasonablePrecautionsNegative

cullenS43AAtomCannotBeReintroducedPositive :
  (candidate :
    Coherence.RegisteredAtomicTest
      cullenAtomicRegistry s43AEngagementEntry) →
  Atomic.gate (Coherence.candidateTest candidate) ≡ BT.pos →
  ⊥
cullenS43AAtomCannotBeReintroducedPositive =
  Coherence.registeredNegativeCannotBeReintroducedPositive
    cullenRegisteredS43ANegative

cullenVicariousFamilyCannotBeReintroducedNegative :
  (candidate :
    Coherence.RegisteredAtomicTest
      cullenAtomicRegistry vicariousFamilyEntry) →
  Atomic.gate (Coherence.candidateTest candidate) ≡ BT.neg →
  ⊥
cullenVicariousFamilyCannotBeReintroducedNegative =
  Coherence.registeredPositiveCannotBeReintroducedNegative
    cullenRegisteredVicariousFamilyPositive

------------------------------------------------------------------------
-- Same sign remains only same sign.
------------------------------------------------------------------------

data RegisteredBreachNegativeEqualsRegisteredS43ANegative : Set where
data RegisteredFamilyPositiveOverridesRegisteredBreachNegative : Set where

registeredNegativeSignsDoNotIdentifyAtoms :
  RegisteredBreachNegativeEqualsRegisteredS43ANegative → ⊥
registeredNegativeSignsDoNotIdentifyAtoms ()

registeredFamilyPositiveDoesNotOverrideBreach :
  RegisteredFamilyPositiveOverridesRegisteredBreachNegative → ⊥
registeredFamilyPositiveDoesNotOverrideBreach ()
