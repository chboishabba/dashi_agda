module DASHI.Physics.Closure.NSTriadKNLuoDyadicHaarRefinementExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Authors: Tuomas Hytönen; Jan van Neerven; Mark Veraar; Lutz Weis.
-- Title: "Analysis in Banach Spaces, Volume I: Martingales and Littlewood--
-- Paley Theory".
-- Springer, 2016.
-- DOI: 10.1007/978-3-319-48520-1.
--
-- PURPOSE
-- Advance the finite eight-point Haar model toward the continuum torus by
-- proving an actual projective-refinement law.  Split every coarse torus point
-- into two equal-mass children.  A cylinder function pulled back from the
-- coarse quotient has exactly the same normalized Haar average on the refined
-- sixteen-point quotient.  The statement is proved for scalars and for the
-- repository's rational Vector3 Bochner carrier.
--
-- Iterating this law gives exact consistency of cylinder averages through the
-- dyadic inverse system.  Constructing the sigma-algebra, countable measure
-- completion, almost-everywhere quotient and completed Bochner integral on
-- T^3 remains a separate constructive-analysis layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact as Coarse
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointHaarBochnerExact as Bochner

record RefinedPoint : Set where
  constructor refined
  field
    coarsePoint : Coarse.BitTorus3
    child : Bool

open RefinedPoint public

oneSixteenth : ℚ
oneSixteenth = Int.+ 1 / 16

refinedSum : (RefinedPoint → ℚ) → ℚ
refinedSum value =
  value (refined Coarse.p000 false) + value (refined Coarse.p000 true)
  + value (refined Coarse.p001 false) + value (refined Coarse.p001 true)
  + value (refined Coarse.p010 false) + value (refined Coarse.p010 true)
  + value (refined Coarse.p011 false) + value (refined Coarse.p011 true)
  + value (refined Coarse.p100 false) + value (refined Coarse.p100 true)
  + value (refined Coarse.p101 false) + value (refined Coarse.p101 true)
  + value (refined Coarse.p110 false) + value (refined Coarse.p110 true)
  + value (refined Coarse.p111 false) + value (refined Coarse.p111 true)

refinedHaarAverage : (RefinedPoint → ℚ) → ℚ
refinedHaarAverage value = oneSixteenth * refinedSum value

pullback :
  (Coarse.BitTorus3 → ℚ) → RefinedPoint → ℚ
pullback value point = value (coarsePoint point)

haarCylinderRefinementInvariant :
  (value : Coarse.BitTorus3 → ℚ) →
  refinedHaarAverage (pullback value) ≡ Coarse.haarAverage value
haarCylinderRefinementInvariant value =
  solve
    ( value Coarse.p000
    ∷ value Coarse.p001
    ∷ value Coarse.p010
    ∷ value Coarse.p011
    ∷ value Coarse.p100
    ∷ value Coarse.p101
    ∷ value Coarse.p110
    ∷ value Coarse.p111
    ∷ [])

refinedBochnerAverage :
  (RefinedPoint → V.Vector3) → V.Vector3
refinedBochnerAverage value =
  V.v3
    (refinedHaarAverage (λ point → V.x (value point)))
    (refinedHaarAverage (λ point → V.y (value point)))
    (refinedHaarAverage (λ point → V.z (value point)))

pullbackVector :
  (Coarse.BitTorus3 → V.Vector3) → RefinedPoint → V.Vector3
pullbackVector value point = value (coarsePoint point)

bochnerCylinderRefinementInvariant :
  (value : Coarse.BitTorus3 → V.Vector3) →
  refinedBochnerAverage (pullbackVector value)
  ≡ Bochner.haarBochnerAverage value
bochnerCylinderRefinementInvariant value =
  V.vectorExt
    (haarCylinderRefinementInvariant (λ point → V.x (value point)))
    (haarCylinderRefinementInvariant (λ point → V.y (value point)))
    (haarCylinderRefinementInvariant (λ point → V.z (value point)))
