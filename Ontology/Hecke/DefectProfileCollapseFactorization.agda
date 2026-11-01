module Ontology.Hecke.DefectProfileCollapseFactorization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( CollapseTime
    ; GeneratorCollapseClass
    ; collapseTime
    ; collapseTime-anchoredTrajectory
    ; collapseTime-balancedComposed
    ; collapseTime-balancedCycle
    ; collapseTime-denseComposed
    ; collapseTime-explicitWidth1
    ; collapseTime-explicitWidth2
    ; collapseTime-explicitWidth3
    ; collapseTime-fullSupportCascade
    ; collapseTime-supportCascade
    ; exitToAnchored
    ; immediateExit
    ; mixedScaleClass
    ; prefixClass
    ; staysOneMoreStep
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily
  using (fullSupportCascade; supportCascade)
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily
  using
    ( anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    )
open import Ontology.Hecke.DefectOrbitCollapsePressure as DOCP
  using
    ( DefectPressureSummary
    ; PressureClass
    ; defectPressureSummaryAt
    ; highPressure
    ; lowPressure
    ; mediumPressure
    ; pressureClass
    )
open import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
  using
    ( CertifiedRepresentativeClass
    ; P2PersistenceTier
    ; certifiedRepresentativeCollapseTime
    ; forcedStableOrbitP2At
    ; orbitCountBandAt
    ; p2PersistenceTierAt
    ; p2PersistenceTier-factors-through-orbitCountBand
    ; tierFromOrbitCountBand
    )
open import Ontology.Hecke.CertifiedRepresentativeOrbitSummaryPersistence as CROSP
  using
    ( CertifiedRepresentativeOrbitSummaryFactorization
    ; canonicalCertifiedRepresentativeOrbitSummaryFactorization
    )
open import Ontology.Hecke.DefectPersistenceRefinement as DPR
  using
    ( CertifiedRepresentativePersistenceRefinementFactorization
    ; canonicalCertifiedRepresentativePersistenceRefinementFactorization
    )

------------------------------------------------------------------------
-- Current factorization scaffold above the pressure layer.
--
-- This is intentionally weaker than a full defect-profile quotient theorem.
-- For now, collapse time factors through a coarse defect-pressure summary
-- built from:
-- - the collapse-derived pressure tier;
-- - the representative `p2` illegal count; and
-- - the representative `p2` orbit forced-stable count.
--
-- A future strengthening should replace this summary with a genuinely
-- Hecke-determined defect-profile quotient.

collapseFromPressure : PressureClass → CollapseTime
collapseFromPressure highPressure = immediateExit
collapseFromPressure mediumPressure = exitToAnchored
collapseFromPressure lowPressure = staysOneMoreStep

collapse-factors-through-pressure :
  ∀ c →
  collapseTime c ≡ collapseFromPressure (pressureClass c)
collapse-factors-through-pressure (prefixClass explicitWidth1) =
  collapseTime-explicitWidth1
collapse-factors-through-pressure (prefixClass explicitWidth2) =
  collapseTime-explicitWidth2
collapse-factors-through-pressure (prefixClass explicitWidth3) =
  collapseTime-explicitWidth3
collapse-factors-through-pressure (prefixClass balancedCycle) =
  collapseTime-balancedCycle
collapse-factors-through-pressure (prefixClass denseComposed) =
  collapseTime-denseComposed
collapse-factors-through-pressure (prefixClass balancedComposed) =
  collapseTime-balancedComposed
collapse-factors-through-pressure (prefixClass anchoredTrajectory) =
  collapseTime-anchoredTrajectory
collapse-factors-through-pressure (mixedScaleClass supportCascade) =
  collapseTime-supportCascade
collapse-factors-through-pressure (mixedScaleClass fullSupportCascade) =
  collapseTime-fullSupportCascade

collapseFromDefectPressureSummary :
  DefectPressureSummary → CollapseTime
collapseFromDefectPressureSummary s =
  collapseFromPressure (DefectPressureSummary.pressureTier s)

collapse-factors-through-defect-pressure-summary :
  ∀ c →
  collapseTime c
    ≡
  collapseFromDefectPressureSummary (defectPressureSummaryAt c)
collapse-factors-through-defect-pressure-summary c =
  collapse-factors-through-pressure c

record CollapsePressureFactorization : Set₁ where
  field
    summary : GeneratorCollapseClass → DefectPressureSummary
    collapseFromSummary : DefectPressureSummary → CollapseTime
    factors :
      ∀ c →
      collapseTime c ≡ collapseFromSummary (summary c)

canonicalCollapsePressureFactorization :
  CollapsePressureFactorization
canonicalCollapsePressureFactorization =
  record
    { summary = defectPressureSummaryAt
    ; collapseFromSummary = collapseFromDefectPressureSummary
    ; factors = collapse-factors-through-defect-pressure-summary
    }

------------------------------------------------------------------------
-- Assumption-guarded future factorization surfaces.
--
-- The current theorem-bearing factorization runs through
-- `DefectPressureSummary`.  These extra surfaces keep the next stronger
-- defect-summary and defect-profile goals explicit without pretending they
-- are already inhabited by the present code.

postulate
  DefectProfile : Set
  DefectSummary : Set

  defectProfile : GeneratorCollapseClass → DefectProfile
  summarizeDefect : DefectProfile → DefectSummary
  collapseFromDefectSummary : DefectSummary → CollapseTime

  ⊥ : Set

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

DefectSummaryFactorizationOK : GeneratorCollapseClass → Set
DefectSummaryFactorizationOK c =
  collapseTime c
    ≡
  collapseFromDefectSummary
    (summarizeDefect (defectProfile c))

SameCollapseSummaryOK :
  GeneratorCollapseClass → GeneratorCollapseClass → Set
SameCollapseSummaryOK c₁ c₂ =
  summarizeDefect (defectProfile c₁)
    ≡
  summarizeDefect (defectProfile c₂)

DifferentCollapseSummaryOK :
  GeneratorCollapseClass → GeneratorCollapseClass → Set
DifferentCollapseSummaryOK c₁ c₂ =
  summarizeDefect (defectProfile c₁)
    ≢
  summarizeDefect (defectProfile c₂)

collapse-factors-through-defect-summary-assumption :
  ∀ c →
  DefectSummaryFactorizationOK c →
  collapseTime c
    ≡
  collapseFromDefectSummary
    (summarizeDefect (defectProfile c))
collapse-factors-through-defect-summary-assumption _ ok = ok

same-collapseTime-same-summary-assumption :
  ∀ c₁ c₂ →
  collapseTime c₁ ≡ collapseTime c₂ →
  SameCollapseSummaryOK c₁ c₂ →
  summarizeDefect (defectProfile c₁)
    ≡
  summarizeDefect (defectProfile c₂)
same-collapseTime-same-summary-assumption _ _ _ ok = ok

different-collapseTime-different-summary-assumption :
  ∀ c₁ c₂ →
  collapseTime c₁ ≢ collapseTime c₂ →
  DifferentCollapseSummaryOK c₁ c₂ →
  summarizeDefect (defectProfile c₁)
    ≢
  summarizeDefect (defectProfile c₂)
different-collapseTime-different-summary-assumption _ _ _ ok = ok

------------------------------------------------------------------------
-- Current exact certified-representative factorization.
--
-- Unlike the pressure-tier factorization above, this one is genuinely
-- collapse-free on its domain: it factors the exact current
-- certified-representative persistence tier through the Hecke-side
-- `forcedStableCountOrbitP2` count band.

record CertifiedRepresentativeOrbitCountFactorization : Set₁ where
  field
    summary : CertifiedRepresentativeClass → Nat
    persistenceTier : CertifiedRepresentativeClass → CRP.P2PersistenceTier
    factor :
      ∀ c →
      persistenceTier c
        ≡
      tierFromOrbitCountBand (orbitCountBandAt c)

certifiedRepresentativeOrbitCountFactorization :
  CertifiedRepresentativeOrbitCountFactorization
certifiedRepresentativeOrbitCountFactorization =
  record
    { summary = forcedStableOrbitP2At
    ; persistenceTier = p2PersistenceTierAt
    ; factor = p2PersistenceTier-factors-through-orbitCountBand
    }

certifiedRepresentativeOrbitSummaryFactorization :
  CertifiedRepresentativeOrbitSummaryFactorization
certifiedRepresentativeOrbitSummaryFactorization =
  canonicalCertifiedRepresentativeOrbitSummaryFactorization

certifiedRepresentativePersistenceRefinementFactorization :
  CertifiedRepresentativePersistenceRefinementFactorization
certifiedRepresentativePersistenceRefinementFactorization =
  canonicalCertifiedRepresentativePersistenceRefinementFactorization
