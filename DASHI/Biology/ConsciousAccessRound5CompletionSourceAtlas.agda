module DASHI.Biology.ConsciousAccessRound5CompletionSourceAtlas where

open import DASHI.Core.Prelude
open import Data.List using (_++_)

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas as R5

------------------------------------------------------------------------
-- Sources added by the SSP-weave, reduced-53, self-indexing, equivariant-
-- Laplacian, modular-stage, Clay-interface, jet, reachability, and exceptional-
-- lattice protocol completion.

borcherdsMoonshineProofSource : R4.SourceRecord
borcherdsMoonshineProofSource =
  R4.sourceRecord
    "Richard E. Borcherds"
    "Monstrous Moonshine and Monstrous Lie Superalgebras"
    "Inventiones Mathematicae"
    1992
    "10.1007/BF01232032"
    "Supports the requirement that moonshine be expressed through a graded Monster module and modular trace functions, not a dimension identity alone."
    "The DASHI 10 times 3^9 plus 54 candidate is not asserted to be a construction of the moonshine module."

fultonHarrisRepresentationSource : R4.SourceRecord
fultonHarrisRepresentationSource =
  R4.sourceRecord
    "William Fulton; Joe Harris"
    "Representation Theory: A First Course"
    "Springer Graduate Texts in Mathematics 129"
    1991
    "10.1007/978-1-4612-0979-9"
    "Supports decomposition into invariant, sign, directional, and higher irreducible sectors and the stability of eigenspaces under commuting symmetry actions."
    "The generic commuting-action interface does not identify the concrete irreps of a proposed Monster, Navier--Stokes, Yang--Mills, or neural realization."

liVitanyiKolmogorovSource : R4.SourceRecord
liVitanyiKolmogorovSource =
  R4.sourceRecord
    "Ming Li; Paul Vitanyi"
    "An Introduction to Kolmogorov Complexity and Its Applications"
    "Springer Texts in Computer Science, fourth edition"
    2019
    "10.1007/978-3-030-11298-1"
    "Supports the distinction between shortest encoded program length, execution length, and machine-relative description complexity."
    "The finite DASHI cost table is not promoted to an exact or computable Kolmogorov complexity."

conwayFRACTRANDOISource : R4.SourceRecord
conwayFRACTRANDOISource =
  R4.sourceRecord
    "John H. Conway"
    "FRACTRAN: A Simple Universal Programming Language for Arithmetic"
    "Open Problems in Communication and Computation"
    1987
    "10.1007/978-1-4612-4808-8_2"
    "Supports guarded execution by signed prime-valuation changes, with denominator exponents acting as inverse or required resources."
    "The finite fifteen-SSP weave does not by itself prove universality or construct a Monster action."

dAnconaCommutatorSource : R4.SourceRecord
dAnconaCommutatorSource =
  R4.sourceRecord
    "Piero D'Ancona"
    "A Short Proof of Commutator Estimates"
    "Journal of Fourier Analysis and Applications"
    2019
    "10.1007/s00041-018-9612-8; correction 10.1007/s00041-019-09724-7"
    "Supplies a primary fractional paired-difference commutator precedent relevant to the separate Navier--Stokes centered-commutator lane."
    "It is not imported as the exact torus Littlewood--Paley (6,3) estimate required by the NS branch; the published correction is retained."

hessChildsTransportCommutatorSource : R4.SourceRecord
hessChildsTransportCommutatorSource =
  R4.sourceRecord
    "Elias Hess-Childs; Matthew Rosenzweig; Sylvia Serfaty"
    "Another Look at Regularity in Transport-Commutator Estimates"
    "Comptes Rendus Mathematique"
    2026
    "10.5802/crmath.837; preprint 10.48550/arXiv.2601.02326"
    "Supplies a recent sharpness and regularity audit for Riesz-type transport commutators, useful as a comparison for the dedicated NS continuum producer."
    "The Riesz-interaction results are not treated as a direct proof of the repository's Navier--Stokes Littlewood--Paley commutator."

viazovskaE8Source : R4.SourceRecord
viazovskaE8Source =
  R4.sourceRecord
    "Maryna S. Viazovska"
    "The Sphere Packing Problem in Dimension 8"
    "Annals of Mathematics"
    2017
    "10.4007/annals.2017.185.3.7"
    "Supplies the rigorous E8 sphere-packing benchmark underlying the fixed eight-dimensional comparison protocol."
    "An embedding with dimension eight or 240 apparent directions is not thereby proved isometric to E8."

cohnLeechPackingSource : R4.SourceRecord
cohnLeechPackingSource =
  R4.sourceRecord
    "Henry Cohn; Abhinav Kumar; Stephen D. Miller; Danylo Radchenko; Maryna Viazovska"
    "The Sphere Packing Problem in Dimension 24"
    "Annals of Mathematics"
    2017
    "10.4007/annals.2017.185.3.8"
    "Supplies the rigorous Leech-lattice sphere-packing benchmark underlying the fixed twenty-four-dimensional comparison protocol."
    "An embedding with dimension twenty-four or 196560 apparent directions is not thereby proved isometric to the Leech lattice."

canonicalRound5CompletionSources : List R4.SourceRecord
canonicalRound5CompletionSources =
  R5.canonicalRound5ExtendedSources
  ++
  (borcherdsMoonshineProofSource
    ∷ fultonHarrisRepresentationSource
    ∷ liVitanyiKolmogorovSource
    ∷ conwayFRACTRANDOISource
    ∷ dAnconaCommutatorSource
    ∷ hessChildsTransportCommutatorSource
    ∷ viazovskaE8Source
    ∷ cohnLeechPackingSource
    ∷ [])

canonicalRound5CompletionSourceCount : Nat
canonicalRound5CompletionSourceCount =
  R4.listCount canonicalRound5CompletionSources

canonicalRound5CompletionSourceCountIsThirtyOne :
  canonicalRound5CompletionSourceCount ≡ 31
canonicalRound5CompletionSourceCountIsThirtyOne = refl
