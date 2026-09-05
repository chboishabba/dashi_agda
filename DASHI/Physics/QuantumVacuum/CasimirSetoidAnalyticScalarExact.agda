module DASHI.Physics.QuantumVacuum.CasimirSetoidAnalyticScalarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact as BishopReuse

------------------------------------------------------------------------
-- SETOID-NATIVE CASIMIR ANALYTIC SCALAR
--
-- This avoids forcing Bishop constructive reals through propositional equality
-- during the analytic calculation.  Equality-facing legacy kernel transport is
-- postponed to one explicit final weld.
------------------------------------------------------------------------

record CasimirSetoidScalarModel : Set₁ where
  field
    real : Spine.SetoidOrderedCompleteReal

    fromNat : Nat → Spine.Carrier real
    pi hbar lightSpeed : Spine.Carrier real

    lengthValue : Q.Length → Spine.Carrier real
    areaValue : Q.Area → Spine.Carrier real

    inverse power3 power4 : Spine.Carrier real → Spine.Carrier real

    energyPerArea : Q.Length → Spine.Carrier real
    pressure : Q.Length → Spine.Carrier real

    energyLaw : (d : Q.Length) →
      Spine._≈_ real
        (energyPerArea d)
        (Spine.neg real
          (Spine._*_ real
            (Spine._*_ real
              (Spine._*_ real pi pi)
              (Spine._*_ real hbar lightSpeed))
            (inverse
              (Spine._*_ real
                (fromNat 720)
                (power3 (lengthValue d))))))

    pressureLaw : (d : Q.Length) →
      Spine._≈_ real
        (pressure d)
        (Spine.neg real
          (Spine._*_ real
            (Spine._*_ real
              (Spine._*_ real pi pi)
              (Spine._*_ real hbar lightSpeed))
            (inverse
              (Spine._*_ real
                (fromNat 240)
                (power4 (lengthValue d))))))

open CasimirSetoidScalarModel public

record BishopCasimirSetoidAuthority : Set₁ where
  field
    model : CasimirSetoidScalarModel
    usesImportedBishopBackend : real model ≡ BishopReuse.casimirSetoidReal

    reciprocalAuthority : Set
    squareRootAuthority : Set
    exponentialAuthority : Set
    piAuthority : Set
    naturalEmbeddingAuthority : Set

    sameObjectSpectralUse : Set
    sameObjectIntegralUse : Set
    sameObjectLimitUse : Set

    reading : String

open BishopCasimirSetoidAuthority public

------------------------------------------------------------------------
-- Final boundary into the older propositional-equality Casimir kernel.
------------------------------------------------------------------------

record SetoidToLegacyCasimirWeld
    (authority : BishopCasimirSetoidAuthority) : Set₁ where
  field
    propositionalQuotient :
      Spine.PropositionalQuotientRealization
        (real (model authority))
    constantsDescend : Set
    spectrumDescends : Set
    renormalisedObservableDescends : Set
    energyLawDescends : Set
    pressureLawDescends : Set
    reading : String

open SetoidToLegacyCasimirWeld public

data SetoidLawAutomaticallyIsPropositionalLaw : Set where

setoidLawNeedsExplicitLegacyWeld :
  SetoidLawAutomaticallyIsPropositionalLaw → ⊥
setoidLawNeedsExplicitLegacyWeld ()
