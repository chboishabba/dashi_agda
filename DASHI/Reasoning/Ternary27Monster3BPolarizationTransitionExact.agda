module DASHI.Reasoning.Ternary27Monster3BPolarizationTransitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.Ternary27FirstTitsMonster3BNormalizerFrontierExact as Frontier

------------------------------------------------------------------------
-- MONSTER-3B SELECTED WORD: POLARIZATION TRANSITION, NOT FIXED 27 ACTION
--
-- Cross-branch donor #1098 now vendors the selected symplectic 12x12 matrix
-- for g2 g1 g2^-1 g1 g2^-1 after normalization into repository coordinates
-- Symplectic12 = X6 + X6*.  Write it in 6x6 blocks
--
--       M = [ A  B ]
--           [ C  D ].
--
-- Exact finite arithmetic gives rank(A)=rank(B)=rank(C)=rank(D)=6.  Thus the
-- off-diagonal blocks are invertible: M does not preserve either chosen
-- Lagrangian X6 or X6*.  In fact M(X6) is transverse to X6 and M(X6*) is
-- transverse to X6*.
--
-- Consequence: the fixed 6+15+6 Schlaefli / first-Tits basis-role chart cannot
-- carry the selected normalizer word as a simple permutation preserving the
-- position / bivector / dual decomposition.  The mathematically natural next
-- layer is an atlas of polarizations, with the 3^6-dimensional Heisenberg /
-- Schrödinger-metaplectic representation carrying the genuine action.
------------------------------------------------------------------------

selectedWord : String
selectedWord = "g2 g1 g2^-1 g1 g2^-1"

selectedWordBlockRanks : String
selectedWordBlockRanks = "rank(A)=rank(B)=rank(C)=rank(D)=6 over GF(3)"

schrodingerDimension : Nat
schrodingerDimension = 729

record SelectedWordPolarizationLocalReceipt : Set where
  constructor selected-word-polarization-local-receipt
  field
    upstreamSelectedWordMatrixPaid : Bool
    upstreamSelectedWordHeisenbergLiftPaid : Bool
    blockARankSixPaidLocally : Bool
    blockBRankSixPaidLocally : Bool
    blockCRankSixPaidLocally : Bool
    blockDRankSixPaidLocally : Bool
    selectedWordPreservesTranslationLagrangian : Bool
    selectedWordPreservesModulationLagrangian : Bool
    imageTranslationTransverseToTranslation : Bool
    imageModulationTransverseToModulation : Bool
    fixedSixFifteenSixRoleChartInvariant : Bool
    polarizationAtlasRequired : Bool
    schrodinger729NaturalActionCarrier : Bool
    monsterAlbertSameActionPaid : Bool
    boundary : String
open SelectedWordPolarizationLocalReceipt public

canonicalSelectedWordPolarizationLocalReceipt : SelectedWordPolarizationLocalReceipt
canonicalSelectedWordPolarizationLocalReceipt =
  selected-word-polarization-local-receipt
    true true
    true true true true
    false false true true false true true false
    "The exact selected 3B normalizer word mixes translation and modulation maximally: all four 6x6 blocks have full rank. Therefore the fixed 6+15+6 role decomposition is a polarization-dependent chart, not an invariant 27-label representation of this word. The appropriate same-action problem moves to polarization transitions and the 729-dimensional Heisenberg/Schrodinger-metaplectic lane; no Monster=Albert action is promoted."

record PolarizationAtlasIntertwiner : Set₁ where
  field
    Polarization : Set
    Chart27 : Polarization → Set
    HeisenbergState729 : Set
    Actor : Set
    actPolarization : Actor → Polarization → Polarization
    act729 : Actor → HeisenbergState729 → HeisenbergState729
    chartTransitionReceipt : Set
    metaplecticIntertwinerReceipt : Set
    firstTitsChartComparisonReceipt : Set
open PolarizationAtlasIntertwiner public

data SharedChartSizeCreatesInvariantAction : Set where

sharedChartDoesNotCreateInvariantAction :
  SharedChartSizeCreatesInvariantAction → {A : Set} → A
sharedChartDoesNotCreateInvariantAction ()
