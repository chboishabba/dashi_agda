module DASHI.Biology.Physical.PadicPhysicalParameterProjectionExact where

------------------------------------------------------------------------
-- p-adic / ultrametric carrier bridge.
--
-- The repository's p-adic cylinders are hierarchical addresses, not a claim
-- that biological physics itself is p-adic.  This module proves the relevant
-- representation fact: a coarse prefix can identify two states whose retained
-- fine digit selects different downstream physical parameters.  Therefore
-- truncation is an information projection and needs a future-safety argument.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.PadicCylinderLODReasoningField as Padic
import DASHI.Geometry.SSP369Ultrametric as U369

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

digit3≢digit6 : U369.digit3 ≢ U369.digit6
digit3≢digit6 ()

parent : Padic.DepthOneAddress
parent = U369.digit3 vcons vnil

fineA fineB : Padic.DepthTwoAddress
fineA = Padic.refineOne parent U369.digit3
fineB = Padic.refineOne parent U369.digit6

sameCoarsePadicPrefix :
  Padic.prefixTwoToOne fineA ≡ Padic.prefixTwoToOne fineB
sameCoarsePadicPrefix = refl

physicalParameter : Padic.DepthTwoAddress → U369.Digit369
physicalParameter (coarse vcons fine vcons vnil) = fine

finePhysicalParametersDiffer :
  physicalParameter fineA ≢ physicalParameter fineB
finePhysicalParametersDiffer = digit3≢digit6

record PadicPhysicalRepresentation (Address Physical : Set) : Set₁ where
  field
    represent : Address → Physical

open PadicPhysicalRepresentation public

canonicalPadicPhysicalRepresentation :
  PadicPhysicalRepresentation Padic.DepthTwoAddress U369.Digit369
canonicalPadicPhysicalRepresentation = record
  { represent = physicalParameter }
