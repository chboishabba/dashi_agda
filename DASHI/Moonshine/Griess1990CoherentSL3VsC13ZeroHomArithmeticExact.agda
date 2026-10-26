module DASHI.Moonshine.Griess1990CoherentSL3VsC13ZeroHomArithmeticExact where

-- Exact finite numerators only, on ORIGINAL preexisting Griess M81
-- coherent-section source. This module does NOT instantiate an Agda
-- finite-group Representation record or assert kernel certified
-- absolute irreducibility / Hom(SL3,J0,grade26)=0.
--
-- PRIORITY: Sah 1974 / Griess 1976 for original abstract splitting;
-- Griess 1990 for THIS order81 Moufang/exceptional Albert source.
-- Character orthogonality is classical (Schur/Maschke). The concrete
-- 5616-element five-bin character enumeration is subsequent exact
-- local computation, with no Agda kernel invocation.
--
-- Reuse existing original owner rather than a new M81/Cube27:
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
import DASHI.Moonshine.Griess1990MoufangCoherentSL3SectionSourceExact as Griess

fullGroupOrder : Nat
fullGroupOrder = 5616

-- Both character squared norms were independently computed from
-- the actual 5616-element corrected-M81 representation.
tracelessAlbertCharacterSquaredNumerator : Nat
tracelessAlbertCharacterSquaredNumerator =
  26 * 26 + 819 * (2 * 2) + 1560 + 104

grade26CharacterSquaredNumerator : Nat
grade26CharacterSquaredNumerator =
  26 * 26 + 819 * (2 * 2) + 1560 * (2 * 2) + 104 * (8 * 8)

tracelessCharacterHasOneNormNumerator :
  tracelessAlbertCharacterSquaredNumerator ≡ fullGroupOrder
tracelessCharacterHasOneNormNumerator = refl

grade26CharacterHasThreeNormNumerator :
  grade26CharacterSquaredNumerator ≡ 3 * fullGroupOrder
grade26CharacterHasThreeNormNumerator = refl

-- Five joint character bins:
-- (χJ0,χgrade26,count) = (26,26,1),(2,2,819),(0,0,3132),
-- (-1,2,1560),(-1,8,104).
-- The signed mixed numerator equals ZERO because each side of
-- the integer equality is exactly 3952.
positiveMixedCharacterContribution : Nat
positiveMixedCharacterContribution =
  26 * 26 + 819 * (2 * 2)

negativeMixedCharacterContribution : Nat
negativeMixedCharacterContribution =
  1560 * 2 + 104 * 8

mixedCharacterNumeratorCancels :
  positiveMixedCharacterContribution ≡ negativeMixedCharacterContribution
mixedCharacterNumeratorCancels = refl

-- The order13 cyclic subgroup restriction has 26D trace 26 at
-- identity, zero on each of 12 nonidentity elements for BOTH reps.
-- Classical character theory then gives complex Hom dimension 52,
-- even though the full SL3(3) Hom dimension is 0.
cyclicHomNumerator : Nat
cyclicHomNumerator = 26 * 26

cyclicHomExact : cyclicHomNumerator ≡ 13 * 52
cyclicHomExact = refl

-- P0 remaining: actual 5616-element Agda group type + actions,
-- source-specific joint-character count certificate, and formal
-- character/equivariant-Hom theorem. This is genuine proof debt.
