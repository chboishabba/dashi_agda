module Ontology.Hecke.RepresentativePressureOrder where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (s≤s; z≤n)

open import DASHI.Pressure using (Pressure; low; medium; high; _⊑p_; _⊔p_)
open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( CertifiedExitToAnchoredClass
    ; CertifiedStayClass
    )
open import Ontology.Hecke.ExitToAnchoredRepresentativeComputations as EARC
  using
    ( ExitToAnchoredRepresentativeComputation
    ; exitToAnchoredComputationAt
    )
open import Ontology.Hecke.ImmediateExitRepresentativeComputations as IERC
  using
    ( CertifiedImmediateExitClass
    ; ImmediateExitRepresentativeComputation
    ; immediateExitComputationAt
    )
open import Ontology.Hecke.StaysOneMoreStepRepresentativeComputations as SSRC
  using
    ( StaysOneMoreStepRepresentativeComputation
    ; computationAt
    )

------------------------------------------------------------------------
-- Generic pressure comparisons across the current Hecke representative lanes.
--
-- This stays theorem-thin on purpose:
-- it does not introduce a new pressure source,
-- it only reuses the exact generic pressure tier already exposed on the
-- representative computation records.

stayRepresentativeGenericPressure :
  CertifiedStayClass → Pressure
stayRepresentativeGenericPressure c =
  SSRC.StaysOneMoreStepRepresentativeComputation.genericPressureTier
    (computationAt c)

anchoredRepresentativeGenericPressure :
  CertifiedExitToAnchoredClass → Pressure
anchoredRepresentativeGenericPressure c =
  EARC.ExitToAnchoredRepresentativeComputation.genericPressureTier
    (exitToAnchoredComputationAt c)

immediateExitRepresentativeGenericPressure :
  CertifiedImmediateExitClass → Pressure
immediateExitRepresentativeGenericPressure c =
  IERC.ImmediateExitRepresentativeComputation.genericPressureTier
    (immediateExitComputationAt c)

stayRepresentative≤anchoredRepresentative :
  ∀ cs ca →
  stayRepresentativeGenericPressure cs
    ⊑p
  anchoredRepresentativeGenericPressure ca
stayRepresentative≤anchoredRepresentative cs ca
  rewrite
    SSRC.StaysOneMoreStepRepresentativeComputation.genericPressureIsLow
      (computationAt cs)
    | EARC.ExitToAnchoredRepresentativeComputation.genericPressureIsMedium
        (exitToAnchoredComputationAt ca)
  = s≤s z≤n

stayRepresentative≤immediateExitRepresentative :
  ∀ cs ce →
  stayRepresentativeGenericPressure cs
    ⊑p
  immediateExitRepresentativeGenericPressure ce
stayRepresentative≤immediateExitRepresentative cs ce
  rewrite
    SSRC.StaysOneMoreStepRepresentativeComputation.genericPressureIsLow
      (computationAt cs)
    | IERC.ImmediateExitRepresentativeComputation.genericPressureIsHigh
        (immediateExitComputationAt ce)
  = s≤s z≤n

anchoredRepresentative≤immediateExitRepresentative :
  ∀ ca ce →
  anchoredRepresentativeGenericPressure ca
    ⊑p
  immediateExitRepresentativeGenericPressure ce
anchoredRepresentative≤immediateExitRepresentative ca ce
  rewrite
    EARC.ExitToAnchoredRepresentativeComputation.genericPressureIsMedium
      (exitToAnchoredComputationAt ca)
    | IERC.ImmediateExitRepresentativeComputation.genericPressureIsHigh
        (immediateExitComputationAt ce)
  = s≤s (s≤s z≤n)

stayRepresentativeJoinAnchored :
  ∀ cs ca →
  stayRepresentativeGenericPressure cs
    ⊔p
  anchoredRepresentativeGenericPressure ca
    ≡
  anchoredRepresentativeGenericPressure ca
stayRepresentativeJoinAnchored cs ca
  rewrite
    SSRC.StaysOneMoreStepRepresentativeComputation.genericPressureIsLow
      (computationAt cs)
    | EARC.ExitToAnchoredRepresentativeComputation.genericPressureIsMedium
        (exitToAnchoredComputationAt ca)
  = refl

representativePressureEnvelope :
  ∀ cs ca ce →
  (stayRepresentativeGenericPressure cs
      ⊔p
   anchoredRepresentativeGenericPressure ca)
      ⊔p
  immediateExitRepresentativeGenericPressure ce
    ≡
  immediateExitRepresentativeGenericPressure ce
representativePressureEnvelope cs ca ce
  rewrite
    SSRC.StaysOneMoreStepRepresentativeComputation.genericPressureIsLow
      (computationAt cs)
    | EARC.ExitToAnchoredRepresentativeComputation.genericPressureIsMedium
        (exitToAnchoredComputationAt ca)
    | IERC.ImmediateExitRepresentativeComputation.genericPressureIsHigh
        (immediateExitComputationAt ce)
  = refl
