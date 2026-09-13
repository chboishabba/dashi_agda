module DASHI.Cognition.PNF.ContinuousOscillatorMemoryRefinementRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Core.RecursiveScaleTransitionExact as Scale

scaleTransitionSurfaceExists : Set₁
scaleTransitionSurfaceExists = Scale.RecursiveScaleTransition
