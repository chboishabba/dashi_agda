module DASHI.Analysis.RHGRHIndexedZeroZetaTransitionSquareExact where

-- P1-F02: a real k -> k' transition square for the *existing* original
-- zero/ζ/ζ² indexed mode carrier; no duplicate phase algebra.
-- Source owners: RHGRHIndexedZeroZetaPhaseResidualWeldExact,
-- SmithFilsingerTimeIndexedTransferExact (retarded indices/source ledgers),
-- TypedHyperfabricActionCrossingTransportExact (ordered steps).
--
-- This proves conditional transition/reflection interchange, with an
-- explicitly supplied source-specific commuting proof. An arbitrary update
-- does NOT commute with conjugation or preserve sign/residual/zero-mode.
-- Full original automorphic source TLiftK/Row0b attachment remains OPEN.
-- Source written, not checked by Agda kernel; no CI.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; true)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Analysis.RHGRHIndexedZeroZetaPhaseResidualWeldExact as Original

private
  module Frame = Original.IndexedZeroPhaseFrame

-- This is a *typed* transition obligation on actual retained fields.
-- No assumption that every arbitrary indexed transition satisfies it.
record SourceIndexedPhaseStep
    {Index Sign Residual : Set}
    (next : Index → Index)
    (step : Original.IndexedZeroPhaseFrame Index Sign Residual →
            Original.IndexedZeroPhaseFrame Index Sign Residual) : Set where
  field
    advancesIndex :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      Frame.index (step f) ≡ next (Frame.index f)

    preservesSign :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      Frame.sign (step f) ≡ Frame.sign f

    preservesResidual :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      Frame.residual (step f) ≡ Frame.residual f

    preservesObservedZero :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      Frame.observedZero (step f) ≡ Frame.observedZero f

    preservesScalarZeroMode :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      Frame.mode f ≡ Original.zeroMode →
      Frame.mode (step f) ≡ Original.zeroMode

    commutesWithReflection :
      (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
      step (Original.reflectFrame f) ≡ Original.reflectFrame (step f)

-- A concrete finite model, analogous to the source's one-step retarded
-- schedule: it changes only k. Unlike an arbitrary time evolution, it
-- provably keeps full phase, sign, residual and observed-zero information.
advanceOne :
  ∀ {Sign Residual} →
  Original.IndexedZeroPhaseFrame Nat Sign Residual →
  Original.IndexedZeroPhaseFrame Nat Sign Residual
advanceOne (Original.indexedZeroPhaseFrame k m s r z) =
  Original.indexedZeroPhaseFrame (suc k) m s r z

advanceOneIsSourceIndexedStep :
  ∀ {Sign Residual} →
  SourceIndexedPhaseStep suc
    (advanceOne {Sign = Sign} {Residual = Residual})
advanceOneIsSourceIndexedStep = record
  { advancesIndex = λ _ → refl
  ; preservesSign = λ _ → refl
  ; preservesResidual = λ _ → refl
  ; preservesObservedZero = λ _ → refl
  ; preservesScalarZeroMode = λ _ p → p
  ; commutesWithReflection = λ _ → refl
  }

-- This is the actual forward k/phase-commuting square, not a double
-- reflection tautology. It uses the exact source transition witness.
indexedReflectionSquare :
  ∀ {Index Sign Residual}
    {next : Index → Index}
    {step : Original.IndexedZeroPhaseFrame Index Sign Residual →
            Original.IndexedZeroPhaseFrame Index Sign Residual}
    (weld : SourceIndexedPhaseStep next step)
    (f : Original.IndexedZeroPhaseFrame Index Sign Residual) →
  step (Original.reflectFrame f) ≡ Original.reflectFrame (step f)
indexedReflectionSquare weld f =
  SourceIndexedPhaseStep.commutesWithReflection weld f

-- Two original k transitions can be composed without losing the sign/
-- residual/zero data or the commuting square.
composeIndexedSteps :
  ∀ {Index Sign Residual}
    {next1 next2 : Index → Index}
    {step1 step2 :
       Original.IndexedZeroPhaseFrame Index Sign Residual →
       Original.IndexedZeroPhaseFrame Index Sign Residual} →
  SourceIndexedPhaseStep next1 step1 →
  SourceIndexedPhaseStep next2 step2 →
  SourceIndexedPhaseStep (λ k → next2 (next1 k))
    (λ f → step2 (step1 f))
composeIndexedSteps {next1 = next1} {next2 = next2}
  {step1 = step1} {step2 = step2} first second = record
  { advancesIndex = λ f →
      trans (SourceIndexedPhaseStep.advancesIndex second (step1 f))
            (cong next2 (SourceIndexedPhaseStep.advancesIndex first f))
  ; preservesSign = λ f →
      trans (SourceIndexedPhaseStep.preservesSign second (step1 f))
            (SourceIndexedPhaseStep.preservesSign first f)
  ; preservesResidual = λ f →
      trans (SourceIndexedPhaseStep.preservesResidual second (step1 f))
            (SourceIndexedPhaseStep.preservesResidual first f)
  ; preservesObservedZero = λ f →
      trans (SourceIndexedPhaseStep.preservesObservedZero second (step1 f))
            (SourceIndexedPhaseStep.preservesObservedZero first f)
  ; preservesScalarZeroMode = λ f zero →
      SourceIndexedPhaseStep.preservesScalarZeroMode second (step1 f)
        (SourceIndexedPhaseStep.preservesScalarZeroMode first f zero)
  ; commutesWithReflection = λ f →
      trans (cong step2 (SourceIndexedPhaseStep.commutesWithReflection first f))
            (SourceIndexedPhaseStep.commutesWithReflection second (step1 f))
  }

-- The original historical sample remains distinct after a time step.
sampleStepPreservesConjugateMode :
  Frame.mode
    (advanceOne Original.balancedObservedZeroWithZetaSquared)
      ≡ Original.zetaSquaredMode
sampleStepPreservesConjugateMode = refl

sampleStepPreservesNonzeroResidual :
  Frame.residual
    (advanceOne Original.balancedObservedZeroWithZeta)
      ≡ Frame.residual Original.balancedObservedZeroWithZeta
sampleStepPreservesNonzeroResidual = refl

sampleStepCommutesWithReflection :
  advanceOne (Original.reflectFrame Original.balancedObservedZeroWithZeta)
    ≡ Original.reflectFrame (advanceOne Original.balancedObservedZeroWithZeta)
sampleStepCommutesWithReflection = refl
