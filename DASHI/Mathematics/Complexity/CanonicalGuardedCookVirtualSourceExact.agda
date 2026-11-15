module DASHI.Mathematics.Complexity.CanonicalGuardedCookVirtualSourceExact where

------------------------------------------------------------------------
-- CANONICAL VIRTUAL SOURCE FOR ONE INDEX-FREE GUARDED COOK DESCRIPTION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat; zero)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Canonical
import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual

canonicalGuardedSource :
  (description : Description.GuardedCookFormulaDescription) →
  Virtual.VirtualFormulaBitSource (Description.formula description)
canonicalGuardedSource description =
  Canonical.canonicalVirtualFormulaBitSource
    (Description.formula description)

readGuardedBit :
  (description : Description.GuardedCookFormulaDescription) →
  Nat → Maybe Agda.Builtin.Bool.Bool
readGuardedBit description index =
  Virtual.readBit (canonicalGuardedSource description) index

queryForRead :
  Description.GuardedCookFormulaDescription →
  Nat → Query.GuardedCookBitQuery
queryForRead = Description.atIndex

queryForReadFormulaExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Query.queryFormula (queryForRead description index)
  ≡ Description.formula description
queryForReadFormulaExact = Description.atIndexFormulaExact

------------------------------------------------------------------------
-- DESCRIPTION-BEARING SOURCE
--
-- Description size is measured by the canonical answer-blind query code at
-- index zero.  Per-read index material is charged separately by the query code
-- and universal generator, rather than hidden in this persistent description.
------------------------------------------------------------------------

describedGuardedSource :
  (description : Description.GuardedCookFormulaDescription) →
  Virtual.DescribedVirtualFormulaBitSource
    (Description.formula description)
describedGuardedSource description = record
  { Virtual.Description = Description.GuardedCookFormulaDescription
  ; Virtual.description = description
  ; Virtual.descriptionSize =
      λ desc → Query.queryBitLength (Description.atIndex desc zero)
  ; Virtual.source = canonicalGuardedSource description
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- No semantic oracle/source witness remains to be constructed for guarded Cook
-- formulas.  The live executable obligation is purely compilation: realize the
-- canonical query function by one finite standard machine and charge its work.
------------------------------------------------------------------------
