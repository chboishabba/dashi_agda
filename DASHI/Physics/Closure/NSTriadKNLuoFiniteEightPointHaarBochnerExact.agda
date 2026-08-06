module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointHaarBochnerExact where

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
-- Lift the concrete normalized Haar average on (Z/2Z)^3 to the repository's
-- rational three-vector carrier.  Translation invariance and preservation of
-- constants are proved componentwise, giving an actual finite vector-valued
-- Haar/Bochner model rather than an assumed integration interface.
--
-- Countable Bochner integration on the continuum torus remains a separate
-- analytic completion theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointTorusHaarExact as Torus

haarBochnerAverage :
  (Torus.BitTorus3 → V.Vector3) → V.Vector3
haarBochnerAverage value =
  V.v3
    (Torus.haarAverage (λ point → V.x (value point)))
    (Torus.haarAverage (λ point → V.y (value point)))
    (Torus.haarAverage (λ point → V.z (value point)))

haarBochnerTranslationInvariant :
  (value : Torus.BitTorus3 → V.Vector3) →
  (shift : Torus.BitTorus3) →
  haarBochnerAverage (λ point → value (Torus.addPoint point shift))
  ≡ haarBochnerAverage value
haarBochnerTranslationInvariant value shift =
  V.vectorExt
    (Torus.translationInvariant (λ point → V.x (value point)) shift)
    (Torus.translationInvariant (λ point → V.y (value point)) shift)
    (Torus.translationInvariant (λ point → V.z (value point)) shift)

haarBochnerConstant :
  (constant : V.Vector3) →
  haarBochnerAverage (λ point → constant) ≡ constant
haarBochnerConstant (V.v3 vx vy vz) =
  V.vectorExt
    (solve (vx ∷ []))
    (solve (vy ∷ []))
    (solve (vz ∷ []))
