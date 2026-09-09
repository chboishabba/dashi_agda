module DASHI.Cognition.PNF.SensibLawCullenRegisteredS5BBlockExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawSourceConditionedAtomicLegalImplicationExact as Implication
import DASHI.Cognition.PNF.SensibLawRegisteredAtomicLegalImplicationExact as Registered
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenAtomicCaseRegistryExact as CullenRegistry

------------------------------------------------------------------------
-- CULLEN REGISTERED s 5B BLOCK
--
-- CLA.s5BThresholdRule is the source-realised DASHI conjunction of the three
-- source-defined s 5B(1) necessary atoms.  On the retained Cullen case fibre,
-- the third atom is canonically registered -1.  A registered implication cannot
-- manufacture a fresh +1 copy of that same atom, so the conjunction cannot run.
------------------------------------------------------------------------

reasonablePrecautionsMembership :
  CLA.reasonablePersonWouldTakePrecautions
  Algebra.∈ Algebra.premises CLA.s5BThresholdRule
reasonablePrecautionsMembership = Algebra.there (Algebra.there Algebra.here)

anyRegisteredReasonablePrecautionsEntryIsNegative :
  (entry : CullenRegistry.CullenAtomicEntry CLA.reasonablePersonWouldTakePrecautions) →
  Atomic.gate
    (DASHI.Cognition.PNF.SensibLawAtomicCaseOutcomeCoherenceExact.canonicalTestFor
      CullenRegistry.cullenAtomicRegistry entry)
  ≡ BT.neg
anyRegisteredReasonablePrecautionsEntryIsNegative CullenRegistry.s5BReasonablePrecautionsEntry = refl

cullenRegisteredS5BThresholdRuleImpossible :
  ∀ {graph facts Enabled} →
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

------------------------------------------------------------------------
-- The blocker is specifically the exact third s 5B atom.  It does not erase
-- the two positive coordinates, change WrongType, negate duty, or determine the
-- vicarious-liability family.
------------------------------------------------------------------------

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
