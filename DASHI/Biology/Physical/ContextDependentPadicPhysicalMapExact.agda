module DASHI.Biology.Physical.ContextDependentPadicPhysicalMapExact where

------------------------------------------------------------------------
-- The p-adic/ultrametric carrier is an address/history representation.  Its
-- physical interpretation may depend on contextual biological state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using ([]; _∷_)

import DASHI.Biology.Physical.PadicPhysicalParameterProjectionExact as Base
import DASHI.Biology.PadicCylinderLODReasoningField as Padic
import DASHI.Geometry.SSP369Ultrametric as U369

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

digit3≢digit6 : U369.digit3 ≢ U369.digit6
digit3≢digit6 ()

record PhysicalContext : Set where
  constructor physicalContext
  field
    accessible : Bool

open PhysicalContext public

contextualParameter :
  PhysicalContext → Padic.DepthTwoAddress → U369.Digit369
contextualParameter (physicalContext false) address = Base.physicalParameter address
contextualParameter (physicalContext true)
  (coarse ∷ U369.digit3 ∷ []) = U369.digit6
contextualParameter (physicalContext true)
  (coarse ∷ U369.digit6 ∷ []) = U369.digit3
contextualParameter (physicalContext true)
  (coarse ∷ U369.digit9 ∷ []) = U369.digit9

closedContext openContext : PhysicalContext
closedContext = physicalContext false
openContext = physicalContext true

sameFineAddressDifferentContextChangesParameter :
  contextualParameter closedContext Base.fineA
  ≢ contextualParameter openContext Base.fineA
sameFineAddressDifferentContextChangesParameter = digit3≢digit6

sameCoarsePrefixStillHidesParameterDifference :
  Padic.prefixTwoToOne Base.fineA ≡ Padic.prefixTwoToOne Base.fineB
sameCoarsePrefixStillHidesParameterDifference = Base.sameCoarsePadicPrefix

closedContextFineParametersDiffer :
  contextualParameter closedContext Base.fineA
  ≢ contextualParameter closedContext Base.fineB
closedContextFineParametersDiffer = Base.finePhysicalParametersDiffer

record ContextDependentRepresentation
  (Address Context Physical : Set) : Set₁ where
  field
    represent : Context → Address → Physical

open ContextDependentRepresentation public

canonicalContextDependentRepresentation :
  ContextDependentRepresentation Padic.DepthTwoAddress PhysicalContext U369.Digit369
canonicalContextDependentRepresentation = record
  { represent = contextualParameter }

-- Therefore Psi : hierarchical carrier -> physical state is more accurately
-- Psi(context,address).  Neither prefix geometry nor symbolic identity alone
-- determines the downstream physical interpretation.
