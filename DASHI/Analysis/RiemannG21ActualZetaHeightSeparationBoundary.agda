module DASHI.Analysis.RiemannG21ActualZetaHeightSeparationBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source boundary for genuine zeta zeros.
--
-- Companion source: Zeta23/Statement.lean defines
--
--   IsNontrivialZero rho := zeta(rho)=0 and 0 < Re rho and Re rho < 1.
--
-- Thus alpha = Re rho - 1/2 lies strictly between -1/2 and 1/2, so the
-- off-line conjugate height |alpha| cannot equal the literal pole height 1/2.
-- The older abstract ZeroConfig in Defs only stores the closed-strip bounds;
-- this strict statement belongs to the actual-zeta specialization and must not
-- be silently imported into every abstract zero configuration.
------------------------------------------------------------------------

record ActualZetaStrictStripSource : Set₁ where
  field
    Zero : Set
    IsNontrivialZero : Zero → Set

    StrictLeftOfOne : Zero → Set
    StrictRightOfZero : Zero → Set

    nontrivialImpliesStrictLeft :
      (rho : Zero) → IsNontrivialZero rho → StrictLeftOfOne rho
    nontrivialImpliesStrictRight :
      (rho : Zero) → IsNontrivialZero rho → StrictRightOfZero rho

    sourceReading : String

open ActualZetaStrictStripSource public

------------------------------------------------------------------------
-- G21 only needs the consequence as a typed height-separation certificate.
-- We keep the analytic arithmetic that converts strict strip inequalities to
-- |alpha| < 1/2 behind an explicit producer rather than fabricating real
-- arithmetic in a Nat-only owner.
------------------------------------------------------------------------

record ActualZetaHeightSeparationProducer
    (source : ActualZetaStrictStripSource) : Set₁ where
  field
    Height : Set
    poleHeight : Height
    offLineHeight : Zero source → Height
    StrictlyBelow : Height → Height → Set

    offLineNoncritical : Zero source → Set

    strictHeightSeparation :
      (rho : Zero source) →
      IsNontrivialZero source rho →
      offLineNoncritical rho →
      StrictlyBelow (offLineHeight rho) poleHeight

    producerReading : String

open ActualZetaHeightSeparationProducer public

record ActualZetaHeightBoundary : Set where
  constructor actualZetaHeightBoundary
  field
    actualZetaSourceUsesOpenCriticalStrip : Bool
    actualZetaSourceUsesOpenCriticalStripIsTrue :
      actualZetaSourceUsesOpenCriticalStrip ≡ true

    abstractZeroConfigUsesOnlyClosedStrip : Bool
    abstractZeroConfigUsesOnlyClosedStripIsTrue :
      abstractZeroConfigUsesOnlyClosedStrip ≡ true

    offLineHeightCannotReachPoleHeightForActualZeta : Bool
    offLineHeightCannotReachPoleHeightForActualZetaIsTrue :
      offLineHeightCannotReachPoleHeightForActualZeta ≡ true

    strictHeightSeparationAloneProvesParityMinors : Bool
    strictHeightSeparationAloneProvesParityMinorsIsFalse :
      strictHeightSeparationAloneProvesParityMinors ≡ false

canonicalActualZetaHeightBoundary : ActualZetaHeightBoundary
canonicalActualZetaHeightBoundary =
  actualZetaHeightBoundary
    true refl
    true refl
    true refl
    false refl
