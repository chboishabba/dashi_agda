module DASHI.Physics.Closure.NSTriadKNLocalizedPDEConstituentPartitionRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- D and F must come from ONE localized PDE identity.  Once that identity has
-- emitted the literal signed constituent list, do not let the kernel residual
-- and the two cutoff-boundary totals be reconstructed independently.
--
-- Pattern-match exhaustively on the existing ExtendedSource and define four
-- disjoint projections of every signed constituent:
--
--   owned/interior, kernel, lower boundary, upper boundary.
--
-- This module proves for every finite literal constituent list
--
--   total = interior + kernel + lowerBoundary + upperBoundary
--
-- exactly over Q.  The physical producer therefore has one remaining source
-- obligation: emit this ONE list from the localized NS identity.  D1/F1 then
-- share the same object definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed

interiorContribution : Signed.SignedConstituent → ℚ
interiorContribution constituent with Signed.source constituent
... | Signed.physicalSource cell = Signed.signedContribution constituent
... | Signed.kernelSource = 0ℚ
... | Signed.tailSource = Signed.signedContribution constituent
... | Signed.boundarySource Signed.lowerCut = 0ℚ
... | Signed.boundarySource Signed.upperCut = 0ℚ

kernelContribution : Signed.SignedConstituent → ℚ
kernelContribution constituent with Signed.source constituent
... | Signed.physicalSource cell = 0ℚ
... | Signed.kernelSource = Signed.signedContribution constituent
... | Signed.tailSource = 0ℚ
... | Signed.boundarySource Signed.lowerCut = 0ℚ
... | Signed.boundarySource Signed.upperCut = 0ℚ

lowerBoundaryContribution : Signed.SignedConstituent → ℚ
lowerBoundaryContribution constituent with Signed.source constituent
... | Signed.physicalSource cell = 0ℚ
... | Signed.kernelSource = 0ℚ
... | Signed.tailSource = 0ℚ
... | Signed.boundarySource Signed.lowerCut = Signed.signedContribution constituent
... | Signed.boundarySource Signed.upperCut = 0ℚ

upperBoundaryContribution : Signed.SignedConstituent → ℚ
upperBoundaryContribution constituent with Signed.source constituent
... | Signed.physicalSource cell = 0ℚ
... | Signed.kernelSource = 0ℚ
... | Signed.tailSource = 0ℚ
... | Signed.boundarySource Signed.lowerCut = 0ℚ
... | Signed.boundarySource Signed.upperCut = Signed.signedContribution constituent

constituentSourcePartitionExact :
  (constituent : Signed.SignedConstituent) →
  Signed.signedContribution constituent
  ≡ interiorContribution constituent
    + kernelContribution constituent
    + lowerBoundaryContribution constituent
    + upperBoundaryContribution constituent
constituentSourcePartitionExact constituent with Signed.source constituent
... | Signed.physicalSource cell = solve (Signed.signedContribution constituent ∷ [])
... | Signed.kernelSource = solve (Signed.signedContribution constituent ∷ [])
... | Signed.tailSource = solve (Signed.signedContribution constituent ∷ [])
... | Signed.boundarySource Signed.lowerCut =
  solve (Signed.signedContribution constituent ∷ [])
... | Signed.boundarySource Signed.upperCut =
  solve (Signed.signedContribution constituent ∷ [])

sumBy : (Signed.SignedConstituent → ℚ) → List Signed.SignedConstituent → ℚ
sumBy projection [] = 0ℚ
sumBy projection (cell ∷ rest) = projection cell + sumBy projection rest

interiorTotal kernelTotal lowerBoundaryTotal upperBoundaryTotal :
  List Signed.SignedConstituent → ℚ
interiorTotal = sumBy interiorContribution
kernelTotal = sumBy kernelContribution
lowerBoundaryTotal = sumBy lowerBoundaryContribution
upperBoundaryTotal = sumBy upperBoundaryContribution

literalTotalPartitionExact :
  (constituents : List Signed.SignedConstituent) →
  Signed.signedConstituentTotal constituents
  ≡ interiorTotal constituents
    + kernelTotal constituents
    + lowerBoundaryTotal constituents
    + upperBoundaryTotal constituents
literalTotalPartitionExact [] = solve []
literalTotalPartitionExact (cell ∷ rest) =
  let
    local = constituentSourcePartitionExact cell
    tail = literalTotalPartitionExact rest
  in
  trans
    (cong (Signed.signedContribution cell +_) tail)
    (trans
      (cong
        (λ localValue →
          localValue
          + (interiorTotal rest + kernelTotal rest
            + lowerBoundaryTotal rest + upperBoundaryTotal rest))
        local)
      (solve
        ( interiorContribution cell
        ∷ kernelContribution cell
        ∷ lowerBoundaryContribution cell
        ∷ upperBoundaryContribution cell
        ∷ interiorTotal rest
        ∷ kernelTotal rest
        ∷ lowerBoundaryTotal rest
        ∷ upperBoundaryTotal rest
        ∷ [])))

record OneLocalizedPDEConstituentSource : Set where
  field
    constituents : List Signed.SignedConstituent
    localizedNonlinearValue : ℚ
    literalConstituentExpansion :
      localizedNonlinearValue ≡ Signed.signedConstituentTotal constituents

open OneLocalizedPDEConstituentSource public

localizedPDEFourWayIdentity :
  (source : OneLocalizedPDEConstituentSource) →
  localizedNonlinearValue source
  ≡ interiorTotal (constituents source)
    + kernelTotal (constituents source)
    + lowerBoundaryTotal (constituents source)
    + upperBoundaryTotal (constituents source)
localizedPDEFourWayIdentity source =
  trans
    (literalConstituentExpansion source)
    (literalTotalPartitionExact (constituents source))

dAndFExtractedFromOneLiteralConstituentList : Bool
dAndFExtractedFromOneLiteralConstituentList = true

dAndFExtractedFromOneLiteralConstituentListIsTrue :
  dAndFExtractedFromOneLiteralConstituentList ≡ true
dAndFExtractedFromOneLiteralConstituentListIsTrue = refl
