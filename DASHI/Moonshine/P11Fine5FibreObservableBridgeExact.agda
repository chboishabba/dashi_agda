module DASHI.Moonshine.P11Fine5FibreObservableBridgeExact where

------------------------------------------------------------------------
-- CONTEXT
--
-- This is the Brandt-side instantiation of the generic quotient/observable
-- discipline extracted from the C9 -> C3 character pullback.  Mathematical
-- category context is recorded in FibreConstantObservableExact; the arithmetic
-- geometry is the source-facing p=11 stack-unweighted five-state cover already
-- constructed in P11FiveStatePositiveHeckeLiftExact.
--
-- DASHI CONTRIBUTION
--
-- Coarse supersingular observables pull back to functions constant on the
-- 2-sheet j=0 fibre and the 3-sheet j=1728 fibre.  Conversely every
-- fibre-constant fine observable is reconstructed from one chosen representative
-- per arithmetic class.  Explicit collisions a0/a1 and b0/b1 show that this
-- quotient factorization does not identify the fine carrier with the coarse one.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.FibreConstantObservableExact as Fibre
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

fine5SectionedQuotient : Fibre.SectionedQuotient Fine.P11Fine5 Geo.P11SupersingularJ
fine5SectionedQuotient = record
  { Fibre.project = Fine.projectFine5
  ; Fibre.representative = Fine.representFine5
  ; Fibre.section = Fine.projectRepresentFine5
  }

coarseClassCode : Geo.P11SupersingularJ → Nat
coarseClassCode Geo.jZeroSS = 0
coarseClassCode Geo.j1728SS = 1

fineClassCode : Fine.P11Fine5 → Nat
fineClassCode = Fibre.pullback Fine.projectFine5 coarseClassCode

fineClassCodeFibreConstant :
  Fibre.FibreConstant Fine.projectFine5 fineClassCode
fineClassCodeFibreConstant =
  Fibre.pullbackIsFibreConstant Fine.projectFine5 coarseClassCode

a0a1SameCoarseObservable : fineClassCode Fine.a0 ≡ fineClassCode Fine.a1
a0a1SameCoarseObservable = refl

b0b1SameCoarseObservable : fineClassCode Fine.b0 ≡ fineClassCode Fine.b1
b0b1SameCoarseObservable = refl

b1b2SameCoarseObservable : fineClassCode Fine.b1 ≡ fineClassCode Fine.b2
b1b2SameCoarseObservable = refl

fineClassCodeReconstructsFromRepresentatives :
  (x : Fine.P11Fine5) →
  fineClassCode x
  ≡ Fibre.pullback
      Fine.projectFine5
      (Fibre.representativeObservable fine5SectionedQuotient fineClassCode)
      x
fineClassCodeReconstructsFromRepresentatives =
  Fibre.fibreConstantObservableReconstructsFromRepresentatives
    fine5SectionedQuotient
    fineClassCode
    fineClassCodeFibreConstant

------------------------------------------------------------------------
-- Nontrivial fibres are explicit.
------------------------------------------------------------------------

a0NotA1 : Fine.a0 ≡ Fine.a1 → ⊥
a0NotA1 ()

b0NotB1 : Fine.b0 ≡ Fine.b1 → ⊥
b0NotB1 ()

aFibreNontrivial : Fibre.NontrivialFibre fine5SectionedQuotient
aFibreNontrivial = record
  { Fibre.left = Fine.a0
  ; Fibre.right = Fine.a1
  ; Fibre.sameProjection = refl
  ; Fibre.distinctFine = a0NotA1
  }

bFibreNontrivial : Fibre.NontrivialFibre fine5SectionedQuotient
bFibreNontrivial = record
  { Fibre.left = Fine.b0
  ; Fibre.right = Fine.b1
  ; Fibre.sameProjection = refl
  ; Fibre.distinctFine = b0NotB1
  }

fine5ProjectionNotInjective :
  ((x y : Fine.P11Fine5) →
    Fine.projectFine5 x ≡ Fine.projectFine5 y → x ≡ y) →
  ⊥
fine5ProjectionNotInjective =
  Fibre.nontrivialFibreBlocksProjectionInjectivity aFibreNontrivial

record P11Fine5FibreObservableBoundary : Set where
  field
    stackCoverSectionedQuotientConstructed : Bool
    stackCoverSectionedQuotientConstructedIsTrue :
      stackCoverSectionedQuotientConstructed ≡ true

    coarseObservablesFibreConstant : Bool
    coarseObservablesFibreConstantIsTrue : coarseObservablesFibreConstant ≡ true

    fibreConstantReconstructionConstructed : Bool
    fibreConstantReconstructionConstructedIsTrue :
      fibreConstantReconstructionConstructed ≡ true

    fineAndCoarseCarriersIdentified : Bool
    fineAndCoarseCarriersIdentifiedIsFalse : fineAndCoarseCarriersIdentified ≡ false

canonicalP11Fine5FibreObservableBoundary : P11Fine5FibreObservableBoundary
canonicalP11Fine5FibreObservableBoundary = record
  { stackCoverSectionedQuotientConstructed = true
  ; stackCoverSectionedQuotientConstructedIsTrue = refl
  ; coarseObservablesFibreConstant = true
  ; coarseObservablesFibreConstantIsTrue = refl
  ; fibreConstantReconstructionConstructed = true
  ; fibreConstantReconstructionConstructedIsTrue = refl
  ; fineAndCoarseCarriersIdentified = false
  ; fineAndCoarseCarriersIdentifiedIsFalse = refl
  }
