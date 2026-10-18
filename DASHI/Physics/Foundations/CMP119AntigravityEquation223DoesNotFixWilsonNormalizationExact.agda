{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEquation223DoesNotFixWilsonNormalizationExact where

------------------------------------------------------------------------
-- MAX-CUT INDEPENDENCE / SOURCE-INTERFACE COMPLETENESS AUDIT.
--
-- CMP119 Sect.2 Eq.(2.23) AS AN ABSTRACT REPOSITORY RECORD cannot fix
-- the Wilson coefficient from runningCoupling.  Demonstrate the issue
-- constructively by giving the *same* g_k and E/R/B/vacuum functions,
-- for ANY user-selected rational coefficient c_k, an exact Eq.(2.23)
-- native state. Its c_k is definitionally the supplied input.
--
-- This is a MODEL OF THE ABSTRACT INTERFACE, NOT the physical paper's
-- selected action. It proves the source-record typing cannot by itself
-- discharge (-c_k) g_k² = 1. A physical normalization proof must come from
-- the literal Wilson action definition or an independent source theorem.
--
-- Attribution: Tadeusz Bałaban, CMP119 (1988), Sect.2 Eq.(2.23).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Data.Unit.Base using (⊤; tt)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Projected

arbitraryWilsonSource :
  (coupling coefficient : Nat → ℚ)
  (wilson regular r b vacuum : Nat → T4.LocalizedAction) →
  Source.CMP119Section2SourceNativeState
    Nat Nat Nat
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
arbitraryWilsonSource coupling coefficient wilson regular r b vacuum =
  record
    { Source.CMP119Section2SourceNativeState.terminalScale = 0
    ; Source.CMP119Section2SourceNativeState.effectiveDensity = λ k → k
    ; Source.CMP119Section2SourceNativeState.backgroundField = λ k → k
    ; Source.CMP119Section2SourceNativeState.fluctuationFields = λ k → k
    ; Source.CMP119Section2SourceNativeState.runningCoupling = coupling
    ; Source.CMP119Section2SourceNativeState.wilsonActionTerm = wilson
    ; Source.CMP119Section2SourceNativeState.regularSmallFieldTerm = regular
    ; Source.CMP119Section2SourceNativeState.rOperationTerm = r
    ; Source.CMP119Section2SourceNativeState.boundaryTerm = b
    ; Source.CMP119Section2SourceNativeState.vacuumEnergy = vacuum
    ; Source.CMP119Section2SourceNativeState.effectiveAction =
        λ k → Canonical.canonicalAssemble
          (coefficient k)
          (wilson k)
          (regular k) (r k) (b k) (vacuum k)
    ; Source.CMP119Section2SourceNativeState.actionAlgebra =
        record
          { Source.CMP119ActionAlgebra.assemble =
              Canonical.canonicalAssemble
          }
    ; Source.CMP119Section2SourceNativeState.wilsonCoefficient = coefficient
    ; Source.CMP119Section2SourceNativeState.equation223 = λ k → refl
    ; Source.CMP119Section2SourceNativeState.ELocalizedAnalytic = λ _ _ → ⊤
    ; Source.CMP119Section2SourceNativeState.RLocalizedAnalytic = λ _ _ → ⊤
    ; Source.CMP119Section2SourceNativeState.BLocalizedAnalytic = λ _ _ → ⊤
    ; Source.CMP119Section2SourceNativeState.RegularBackground = λ _ _ → ⊤
    ; Source.CMP119Section2SourceNativeState.CompleteDensityForm = λ _ _ → ⊤
    ; Source.CMP119Section2SourceNativeState.eSector = λ _ → tt
    ; Source.CMP119Section2SourceNativeState.rSector = λ _ → tt
    ; Source.CMP119Section2SourceNativeState.bSector = λ _ → tt
    ; Source.CMP119Section2SourceNativeState.regularBackground = λ _ → tt
    ; Source.CMP119Section2SourceNativeState.completeDensityForm = λ _ → tt
    }

freeWilsonCoefficientIsInput :
  ∀ coupling coefficient wilson regular r b vacuum k →
  Source.wilsonCoefficient
    (arbitraryWilsonSource coupling coefficient wilson regular r b vacuum) k
  ≡ coefficient k
freeWilsonCoefficientIsInput coupling coefficient wilson regular r b vacuum k =
  refl

freeRunningCouplingIsInput :
  ∀ coupling coefficient wilson regular r b vacuum k →
  Source.runningCoupling
    (arbitraryWilsonSource coupling coefficient wilson regular r b vacuum) k
  ≡ coupling k
freeRunningCouplingIsInput coupling coefficient wilson regular r b vacuum k =
  refl

------------------------------------------------------------------------
-- EVEN AFTER EXACT RATIONAL ACTION INTERPRETATION AND UNIT WILSON BASIS,
-- Eq.(2.23) still leaves c_k free. The missing product normalization is a
-- genuinely separate physics statement, not concealed inside the algebra
-- interpretation. This deliberately passes the existing selected Eq.223
-- source projector contract without making any claim of physical selection.
------------------------------------------------------------------------

sourceWithUnitWilson :
  (coupling coefficient : Nat → ℚ)
  (regular r b vacuum : Nat → T4.LocalizedAction) →
  Source.CMP119Section2SourceNativeState
    Nat Nat Nat
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
sourceWithUnitWilson coupling coefficient regular r b vacuum =
  arbitraryWilsonSource coupling coefficient
    (λ _ → T4.plaquetteBasisAction)
    regular r b vacuum

unitWilsonSourceHasActualProjectorAlgebra :
  ∀ coupling coefficient regular r b vacuum →
  Projected.SelectedEq223RationalActionInterpretation
    (sourceWithUnitWilson coupling coefficient regular r b vacuum)
unitWilsonSourceHasActualProjectorAlgebra
    coupling coefficient regular r b vacuum = record
  { Projected.SelectedEq223RationalActionInterpretation.sourceAssemblyPreservesLocalizedAction =
      λ _ _ _ _ _ _ → refl
  ; Projected.SelectedEq223RationalActionInterpretation.sourceWilsonBasisUnit =
      λ _ → T4.plaquetteCoefficientOfPlaquetteBasis
  }

unitWilsonSourceCoefficientStillFree :
  ∀ coupling coefficient regular r b vacuum k →
  Source.wilsonCoefficient
    (sourceWithUnitWilson coupling coefficient regular r b vacuum) k
  ≡ coefficient k
unitWilsonSourceCoefficientStillFree
    coupling coefficient regular r b vacuum k = refl
