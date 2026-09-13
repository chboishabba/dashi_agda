module DASHI.Cognition.PNF.SensibLawCullenRegisteredS5BBlockExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact as Coherence
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as Implication
import DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact as Registered
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenAtomicCaseRegistryExact as CullenRegistry

reasonablePrecautionsMembership :
  CLA.reasonablePersonWouldTakePrecautions
  Algebra.∈ Algebra.premises CLA.s5BThresholdRule
reasonablePrecautionsMembership = Algebra.there (Algebra.there Algebra.here)

anyRegisteredReasonablePrecautionsEntryIsNegative :
  (entry : CullenRegistry.CullenAtomicEntry CLA.reasonablePersonWouldTakePrecautions) →
  Atomic.gate
    (Coherence.canonicalTestFor CullenRegistry.cullenAtomicRegistry entry)
  ≡ BT.neg
anyRegisteredReasonablePrecautionsEntryIsNegative CullenRegistry.s5BReasonablePrecautionsEntry = refl

cullenRegisteredS5BThresholdRuleImpossible :
  ∀ {graph : Algebra.LegalGraph}
    {facts : Algebra.FactSet}
    {Enabled : Algebra.LegalRule → Set} →
  (input :
    Implication.SourceConditionedAtomicLegalImplication
      graph facts Enabled CLA.s5BThresholdRule) →
  (registered :
    Registered.RegisteredSourceConditionedAtomicLegalImplication
      CullenRegistry.cullenAtomicRegistry
      CullenRegistry.cullenCaseContext
      input) →
  ⊥
cullenRegisteredS5BThresholdRuleImpossible input registered =
  Registered.registeredNegativePremiseBlocksImplication
    registered
    reasonablePrecautionsMembership
    (anyRegisteredReasonablePrecautionsEntryIsNegative
      (Registered.premiseEntry registered reasonablePrecautionsMembership))

data RegisteredS5BBlockerNegatesForeseeability : Set where
data RegisteredS5BBlockerNegatesNotInsignificant : Set where
data RegisteredS5BBlockerChangesWrongType : Set where
data RegisteredS5BBlockerErasesDuty : Set where
data RegisteredS5BBlockerChoosesLiabilityFamily : Set where

blockerDoesNotNegateForeseeability : RegisteredS5BBlockerNegatesForeseeability → ⊥
blockerDoesNotNegateForeseeability ()

blockerDoesNotNegateNotInsignificant : RegisteredS5BBlockerNegatesNotInsignificant → ⊥
blockerDoesNotNegateNotInsignificant ()

blockerDoesNotChangeWrongType : RegisteredS5BBlockerChangesWrongType → ⊥
blockerDoesNotChangeWrongType ()

blockerDoesNotEraseDuty : RegisteredS5BBlockerErasesDuty → ⊥
blockerDoesNotEraseDuty ()

blockerDoesNotChooseFamily : RegisteredS5BBlockerChoosesLiabilityFamily → ⊥
blockerDoesNotChooseFamily ()
