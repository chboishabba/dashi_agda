module DASHI.Moonshine.Y443DGLWeakCertificateNoGoExact where

------------------------------------------------------------------------
-- IMPORTANT COUNTEREXAMPLE TO PREVIOUS DGL ROUTE ABI
--
-- The current DGL "HolomorphicC2Certificate" and
-- "HigherGradeBoundCertificate" are NOT SOURCE-SOUND standalone proofs:
-- their module/quotient carriers and dimension identification "Set"
-- propositions may be chosen arbitrarily, with no actual selected VOA
-- module classification, actual C2 quotient or honest grade dimensions.
--
-- We explicitly inhabit both certificates for EVERY PAIR of abstract
-- VOA-core records using singleton types / constant-zero counts.
-- Hence NO theorem may promote these certificates alone to FLM
-- uniqueness. The stronger published mathematical DGL hypothesis is
-- unaffected; the ABI requires actual identified module / grade data.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443DGLUniquenessSelectedFLMExact as DGL

module ArbitraryWeakVOAs
  (V canonical : VOA.VertexOperatorAlgebra) where
  module U = DGL.Selected V canonical

  vacuousHolomorphicC2 :
    U.HolomorphicC2Certificate
  vacuousHolomorphicC2 = record
    { U.IrreducibleModuleOfSelected = ⊤
    ; U.selectedVacuumModule = tt
    ; U.allIrreduciblesAreVacuum = λ { tt → refl }
    ; U.C2QuotientOfSelected = ⊤
    ; U.c2FiniteDimension = suc zero
    ; U.c2Basis = λ _ → tt
    ; U.c2SpanningCertificate = ⊤
    ; U.c2SpanningIsProved = tt
    }

  vacuousHigherGradeBound :
    U.HigherGradeBoundCertificate
  vacuousHigherGradeBound = record
    { U.selectedDimension = λ _ → zero
    ; U.canonicalDimension = λ _ → zero
    ; U.gradeDimensionIdentification = ⊤
    ; U.gradeDimensionIdentificationProved = tt
    ; U.selectedSimpleVOA = ⊤
    ; U.selectedSimpleVOAProved = tt
    ; U.eachGradeBoundFromThree = λ _ → DGL.zeroLe
    }

-- The only legitimate use of DGL uniqueness is with independently
-- source-certified hypotheses about the actual selected VOA, including
-- proof-relevant C2 quotient/irreducible module and graded dimension
-- theory. The older ad hoc route record is now an explicit NO-GO
-- and must be strengthened before production theorem promotion.
