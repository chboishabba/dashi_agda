module DASHI.Biology.ConsciousAccessRound4SourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attributed source atlas for p-adic hierarchy, pattern selection,
-- crystallisation, defects, and cut-and-project order.

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    importedRole : String
    excludedPromotion : String

open SourceRecord public

serreArithmeticSource : SourceRecord
serreArithmeticSource =
  sourceRecord
    "Jean-Pierre Serre"
    "A Course in Arithmetic"
    "Graduate Texts in Mathematics 7, Springer"
    1973
    "10.1007/978-1-4684-9884-4"
    "Supports the separation of finite residue systems, p-adic completions, and ordinary integer notation."
    "The finite DASHI prefix carrier is not asserted to be a completed implementation of all p-adic analysis."

robertPadicAnalysisSource : SourceRecord
robertPadicAnalysisSource =
  sourceRecord
    "Alain M. Robert"
    "A Course in p-adic Analysis"
    "Graduate Texts in Mathematics 198, Springer"
    2000
    "10.1007/978-1-4757-3254-2"
    "Supports ultrametric continuity, cylinder refinement, and Euclidean observation models of p-adic spaces."
    "The Morton-like rendering map is not promoted to a canonical p-adic embedding or isometry."

swiftHohenbergSource : SourceRecord
swiftHohenbergSource =
  sourceRecord
    "J. Swift; P. C. Hohenberg"
    "Hydrodynamic Fluctuations at the Convective Instability"
    "Physical Review A"
    1977
    "10.1103/PhysRevA.15.319"
    "Motivates finite-wavenumber shell instability and the six-direction mode-star abstraction."
    "The finite mode carrier is not a solved continuum Swift-Hohenberg PDE."

crossHohenbergSource : SourceRecord
crossHohenbergSource =
  sourceRecord
    "M. C. Cross; P. C. Hohenberg"
    "Pattern Formation Outside of Equilibrium"
    "Reviews of Modern Physics"
    1993
    "10.1103/RevModPhys.65.851"
    "Supports coefficient-dependent amplitude competition, symmetry breaking, coarsening, and defects."
    "The exact Nat-valued branch scores are not calibrated amplitude coefficients."

lifshitzPetrichSource : SourceRecord
lifshitzPetrichSource =
  sourceRecord
    "Ron Lifshitz; Dean M. Petrich"
    "Theoretical Model for Faraday Waves with Multiple-Frequency Forcing"
    "Physical Review Letters"
    1997
    "10.1103/PhysRevLett.79.1261"
    "Motivates separating multi-length-scale quasiperiodic mode selection from a one-shell periodic model."
    "A triadic nine-lift alone is not claimed to generate twelvefold quasiperiodic order."

kibbleDefectSource : SourceRecord
kibbleDefectSource =
  sourceRecord
    "T. W. B. Kibble"
    "Topology of Cosmic Domains and Strings"
    "Journal of Physics A: Mathematical and General"
    1976
    "10.1088/0305-4470/9/8/029"
    "Motivates defects as compatibility or homotopy residuals after symmetry breaking."
    "The finite grain-boundary witness is not a cosmological defect calculation."

moodyModelSetSource : SourceRecord
moodyModelSetSource =
  sourceRecord
    "Robert V. Moody"
    "Model Sets: A Survey"
    "From Quasicrystals to More Complex Systems"
    2000
    "10.1007/978-3-662-04253-3_6"
    "Supports the cut-and-project distinction between physical coordinates and internal acceptance space."
    "The finite acceptance-window example is not an irrational model-set theorem."

baakeGrimmAperiodicSource : SourceRecord
baakeGrimmAperiodicSource =
  sourceRecord
    "Michael Baake; Uwe Grimm"
    "Aperiodic Order, Volume 1: A Mathematical Invitation"
    "Cambridge University Press"
    2013
    "10.1017/CBO9781139025256"
    "Supports the distinction between periodic crystallographic order, aperiodic order, and projection-dependent symmetry."
    "No physical quasicrystal is inferred from a finite internal label refinement."

canonicalRound4Sources : List SourceRecord
canonicalRound4Sources =
  serreArithmeticSource
  ∷ robertPadicAnalysisSource
  ∷ swiftHohenbergSource
  ∷ crossHohenbergSource
  ∷ lifshitzPetrichSource
  ∷ kibbleDefectSource
  ∷ moodyModelSetSource
  ∷ baakeGrimmAperiodicSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

canonicalRound4SourceCount : Nat
canonicalRound4SourceCount = listCount canonicalRound4Sources

canonicalRound4SourceCountIsEight : canonicalRound4SourceCount ≡ 8
canonicalRound4SourceCountIsEight = refl
