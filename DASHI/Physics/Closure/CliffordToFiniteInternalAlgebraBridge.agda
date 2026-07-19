module DASHI.Physics.Closure.CliffordToFiniteInternalAlgebraBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTC
import DASHI.Physics.StandardModel.FiniteRealStarAlgebraCandidates as FCA
import DASHI.Physics.StandardModel.FiniteInternalAlgebraClassificationTarget as FIC

------------------------------------------------------------------------
-- Narrow bridge from the already-named quadratic/Clifford closure lane to the
-- finite internal algebra classification problem.
--
-- This module does not manufacture Standard-Model uniqueness from a Clifford
-- presentation.  It records the exact additional theorem needed.  Once a
-- classification witness is supplied, the internal algebra result follows by
-- ordinary application rather than by interpretation.
------------------------------------------------------------------------

record CliffordToFiniteInternalAlgebraBridge : Setω where
  field
    spacetimeClifford : QTC.QuadraticToCliffordBridgeTheorem
    internalClassification : FIC.FiniteInternalAlgebraClassification

open CliffordToFiniteInternalAlgebraBridge public

internalAlgebraForcedToStandardModelSpine :
  (bridge : CliffordToFiniteInternalAlgebraBridge) →
  (A : FCA.FiniteRealStarAlgebra) →
  (D : FIC.FiniteSpectralData A) →
  FIC.C1C5Admissible A D →
  A ≡ FCA.standardModelSpine
internalAlgebraForcedToStandardModelSpine bridge =
  FIC.uniqueUnderC1C5
    (CliffordToFiniteInternalAlgebraBridge.internalClassification bridge)

canonicalSpacetimeCliffordAvailable :
  QTC.QuadraticToCliffordBridgeTheorem
canonicalSpacetimeCliffordAvailable =
  QTC.canonicalQuadraticToCliffordBridgeTheorem
