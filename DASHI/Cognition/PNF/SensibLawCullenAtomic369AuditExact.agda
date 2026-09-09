module DASHI.Cognition.PNF.SensibLawCullenAtomic369AuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import Base369 as Base
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Cognition.PNF.SensibLawSourceRuleDialectic369CrossPollinationExact as Legal369
import DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact as S5B
import DASHI.Cognition.PNF.SensibLawCullenS43ASpecialStatutoryPowerAtomicExact as S43A
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Vicarious

------------------------------------------------------------------------
-- CULLEN ATOMIC 369 AUDIT
--
-- The 27 carrier is only an audit serialization of three exact atomic gates.
-- It neither merges the legal atoms nor creates a legal conclusion.
------------------------------------------------------------------------

cullenS5B27 : Ternary.SynthesisChoice27
cullenS5B27 = Legal369.atomicTestsTo27
  S5B.cullenForeseeableAtom
  S5B.cullenNotInsignificantAtom
  S5B.cullenReasonablePrecautionsAtom

cullenS5B27IsPositivePositiveNegative :
  cullenS5B27
  ≡ Ternary.makeSynthesisChoice Base.tri-high Base.tri-high Base.tri-low
cullenS5B27IsPositivePositiveNegative = refl

------------------------------------------------------------------------
-- A second 27-cell keeps three different downstream axes distinct:
--   s 5B(1)(c) reasonable-precautions fit = -1
--   s 43A special-statutory-power engagement = -1
--   vicarious-liability family recognition = +1
--
-- Same sign does not mean same atom, same source, or same legal effect.
------------------------------------------------------------------------

cullenDownstream27 : Ternary.SynthesisChoice27
cullenDownstream27 = Legal369.atomicTestsTo27
  S5B.cullenReasonablePrecautionsAtom
  S43A.cullenS43ABasedOnAtom
  Vicarious.cullenVicariousFamilyAtom

cullenDownstream27IsNegativeNegativePositive :
  cullenDownstream27
  ≡ Ternary.makeSynthesisChoice Base.tri-low Base.tri-low Base.tri-high
cullenDownstream27IsNegativeNegativePositive = refl

data SameNegativeGateMeansSameLegalAtom : Set where
data Same27CellMeansSameSourceHistory : Set where
data VicariousPositiveOverridesBreachNegative : Set where

data S43ANegativeIsBreachNegative : Set where

sameSignDoesNotIdentifyAtom : SameNegativeGateMeansSameLegalAtom → ⊥
sameSignDoesNotIdentifyAtom ()

same27CellDoesNotRestoreSources : Same27CellMeansSameSourceHistory → ⊥
same27CellDoesNotRestoreSources ()

familyPositiveDoesNotOverrideBreachFailure : VicariousPositiveOverridesBreachNegative → ⊥
familyPositiveDoesNotOverrideBreachFailure ()

s43ANegativeDoesNotEqualBreachNegative : S43ANegativeIsBreachNegative → ⊥
s43ANegativeDoesNotEqualBreachNegative ()
