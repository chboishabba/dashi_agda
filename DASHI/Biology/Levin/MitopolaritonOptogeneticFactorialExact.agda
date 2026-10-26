module DASHI.Biology.Levin.MitopolaritonOptogeneticFactorialExact where

-- A causal experimental-design interface for mid-IR mitochondrial
-- illumination x classical light-gated-channel optogenetics.
-- Factorial contrast is algebra; no experiment or effect size is asserted.
-- Source context: Liu et al. 2012 Nature 10.1038/nature11028;
-- Ramirez et al. 2013 Science 10.1126/science.1239073;
-- Yang, Gu, Song 2026 bioRxiv 10.64898/2026.09.10.750628.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Biology.Levin.MitopolaritonTwoModeSpectrumExact as Spectra

data MitoStimulus : Set where
  sham midIR71 midIR87 midIR537 : MitoStimulus

data OpsinStimulus : Set where
  opsinOff opsinOn : OpsinStimulus

record ExperimentalArm : Set where
  constructor arm
  field
    mito : MitoStimulus
    opsin : OpsinStimulus

record FactorialResponse : Set where
  constructor factorial-response
  field
    y00 y10 y01 y11 : ℚ
  -- Units/outcome and matching protocol must be declared by the consumer.
open FactorialResponse public

interactionContrast : FactorialResponse → ℚ
interactionContrast r =
  (y11 r - y10 r) - (y01 r - y00 r)

zeroInteractionForAdditiveModel :
  (baseline mitoEffect opsinEffect : ℚ) →
  ((baseline + mitoEffect + opsinEffect) -
   (baseline + mitoEffect)) -
  ((baseline + opsinEffect) - baseline) ≡
  (baseline - baseline)
zeroInteractionForAdditiveModel baseline mitoEffect opsinEffect =
  solve (baseline ∷ mitoEffect ∷ opsinEffect ∷ [])
