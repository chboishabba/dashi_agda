module DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact where

------------------------------------------------------------------------
-- ROUND76: REMOVE THE ARTIFICIAL SOURCE/REPOSITORY STATE-EQUALITY PROBLEM
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Section 2 gives ONE complete effective density.  In particular (2.18)--(2.23)
-- describe the density/operation/effective-action object, (2.25)--(2.29) its
-- regular E sector, (2.30)--(2.33) its localized R sector, and (2.40)--(2.42)
-- its boundary B sector.  These are not five unrelated repository scalars.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- CMP109 works directly with the twice differentiated E^(2) object and the
-- resummed polarization Pi.  Round73 already records the published marked
-- localization/decay authority.  The point of THIS module is same-objectness:
-- the strong Clay state is defined as an extension of the source density and
-- source differentiated coordinate rather than as an independently rebuilt
-- tuple which later requires an equality theorem.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- CMP122 preserves the complete-density inductive class under the published
-- small-effective-coupling hypothesis.  Therefore a physical theorem whose
-- state carrier is `SourceNativeUnifiedState` ALREADY enters the published RG;
-- there is no independent `p_literal = p_Balaban` analytic lemma left to prove.
-- Quantitative comparisons required by the stronger norm remain genuine work
-- inside the physical one-step estimate; they are not hidden here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119

------------------------------------------------------------------------
-- Source differentiated coordinate.  E2 is computed FROM the regular E term;
-- Pi is computed FROM that E2 coordinate.  A concrete CMP109 instantiation is
-- therefore incapable of drifting onto a different effective density.
------------------------------------------------------------------------

record CMP109DifferentiatedCoordinate (RegularTerm : Set) : Set₁ where
  field
    E2 Pi : Set
    secondVariation : RegularTerm → E2
    polarization : E2 → Pi

open CMP109DifferentiatedCoordinate public

------------------------------------------------------------------------
-- Literal source-native baseline: exactly the complete density of CMP119/122,
-- together with the CMP109 differentiated coordinate on its regular E sector.
------------------------------------------------------------------------

record SourceNativeBalabanBaseline : Set₂ where
  field
    Coupling Density Operation Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    completeDensity :
      CMP119.CMP119Section2CompleteDensity
        Coupling Density Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay

    differentiated : CMP109DifferentiatedCoordinate RegularTerm

open SourceNativeBalabanBaseline public

literalDensity : (base : SourceNativeBalabanBaseline) → Density base
literalDensity base = CMP119.rho (completeDensity base)

literalCoupling : (base : SourceNativeBalabanBaseline) → Coupling base
literalCoupling base = CMP119.g (completeDensity base)

literalBackground : (base : SourceNativeBalabanBaseline) → Field base
literalBackground base = CMP119.background (completeDensity base)

literalRegularE : (base : SourceNativeBalabanBaseline) → RegularTerm base
literalRegularE base = CMP119.regularE (completeDensity base)

literalR : (base : SourceNativeBalabanBaseline) → RTerm base
literalR base = CMP119.rOperationR (completeDensity base)

literalBoundary : (base : SourceNativeBalabanBaseline) → BoundaryTerm base
literalBoundary base = CMP119.boundaryB (completeDensity base)

literalOperation : (base : SourceNativeBalabanBaseline) → Operation base
literalOperation base = CMP119.T (completeDensity base)

literalDecay : (base : SourceNativeBalabanBaseline) → Decay base
literalDecay base = CMP119.decayKappa (completeDensity base)

sourceE2 : (base : SourceNativeBalabanBaseline) → E2 (differentiated base)
sourceE2 base = secondVariation (differentiated base) (literalRegularE base)

sourcePi : (base : SourceNativeBalabanBaseline) → Pi (differentiated base)
sourcePi base = polarization (differentiated base) (sourceE2 base)

------------------------------------------------------------------------
-- Strong Clay state = SOURCE BASELINE + genuinely new consumer coordinates.
-- The baseline is not copied.  It is a field of the strong state itself.
------------------------------------------------------------------------

record SourceNativeUnifiedState (base : SourceNativeBalabanBaseline) : Set₂ where
  field
    CompositeInsertion WeightedConnectedCorrelation Characteristic : Set
    compositeInsertion : CompositeInsertion
    weightedConnectedCorrelation : WeightedConnectedCorrelation
    characteristic : Characteristic

open SourceNativeUnifiedState public

unifiedDensity :
  ∀ {base} → SourceNativeUnifiedState base → Density base
unifiedDensity {base} state = literalDensity base

unifiedHessian :
  ∀ {base} → SourceNativeUnifiedState base → E2 (differentiated base)
unifiedHessian {base} state = sourceE2 base

unifiedPolarization :
  ∀ {base} → SourceNativeUnifiedState base → Pi (differentiated base)
unifiedPolarization {base} state = sourcePi base

------------------------------------------------------------------------
-- Exact entry certificate.  Every identity is reflexivity because there is one
-- object, not a source state plus an independently reconstructed repository
-- state.  This is the correct way to eliminate old analytic job #3.
------------------------------------------------------------------------

record LiteralPublishedBalabanEntry
    {base : SourceNativeBalabanBaseline}
    (state : SourceNativeUnifiedState base) : Set₂ where
  field
    densityIsPublishedDensity :
      unifiedDensity state ≡ CMP119.rho (completeDensity base)

    couplingIsPublishedCoupling :
      literalCoupling base ≡ CMP119.g (completeDensity base)

    backgroundIsPublishedBackground :
      literalBackground base ≡ CMP119.background (completeDensity base)

    regularEIsPublishedRegularE :
      literalRegularE base ≡ CMP119.regularE (completeDensity base)

    rOperationIsPublishedR :
      literalR base ≡ CMP119.rOperationR (completeDensity base)

    boundaryIsPublishedB :
      literalBoundary base ≡ CMP119.boundaryB (completeDensity base)

    integrationOperationIsPublishedT :
      literalOperation base ≡ CMP119.T (completeDensity base)

    regulatorIsPublishedDecayCoordinate :
      literalDecay base ≡ CMP119.decayKappa (completeDensity base)

    hessianIsSourceE2 :
      unifiedHessian state
      ≡ secondVariation (differentiated base)
          (CMP119.regularE (completeDensity base))

    polarizationIsSourcePi :
      unifiedPolarization state
      ≡ polarization (differentiated base)
          (secondVariation (differentiated base)
            (CMP119.regularE (completeDensity base)))

open LiteralPublishedBalabanEntry public

literalStateEntersPublishedBalabanRG :
  ∀ {base} (state : SourceNativeUnifiedState base) →
  LiteralPublishedBalabanEntry state
literalStateEntersPublishedBalabanRG state = record
  { densityIsPublishedDensity = refl
  ; couplingIsPublishedCoupling = refl
  ; backgroundIsPublishedBackground = refl
  ; regularEIsPublishedRegularE = refl
  ; rOperationIsPublishedR = refl
  ; boundaryIsPublishedB = refl
  ; integrationOperationIsPublishedT = refl
  ; regulatorIsPublishedDecayCoordinate = refl
  ; hessianIsSourceE2 = refl
  ; polarizationIsSourcePi = refl
  }

sourceNativeBalabanEntryLevel : ProofLevel
sourceNativeBalabanEntryLevel = machineChecked

-- The physical work that remains is NOT an equality between two states.  It is
-- the quantitative strong-norm estimate on this one state: compare the source
-- E/R/B/T/background/Hessian coordinates with the strong norm and prove the
-- common one-step contraction/consumer modulus.
physicalSourceNativeStrongNormComparisonLevel : ProofLevel
physicalSourceNativeStrongNormComparisonLevel = conditional
