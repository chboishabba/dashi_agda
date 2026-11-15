module DASHI.Analysis.BishopOriginalEtaPairBlockTelescopingExact where

------------------------------------------------------------------------
-- ACTUAL MURRAY/BISHOP ORIGINAL ETA: ALL-CUTOFF SHIFTED PAIR TAIL.
--
-- The original Round11 even/odd eta block is
--   a(2j) - a(2j+1)
-- on BishopOriginalDirichletEtaFinitePairingExact.originalEtaBlock.
-- This source theorem REUSES that very block, that very finite
-- prefix and the literal original selected nat-log/complex exp term.
--
-- A genuinely constructive finite identity on the original Bishop
-- real setoid, proved in both complex coordinates:
--
--   eta_(n+m) = eta_n + sum_{j=0}^{m-1}
--                          [a(2(n+j)) - a(2(n+j)+1)].
--
-- This is the exact shifted-pair/telescoping entry point for the
-- Abel uniform tail (BishopOriginalEtaAbelUniformTail20261114.md).
-- The difficult analytic step remains an original source estimate
--   |a(j)-a(j+1)| <= (|s|/sigma) Delta j^{-sigma},
-- plus the actual Bishop log equality, complex differentiation,
-- fundamental theorem, norms and uniform Cauchy modulus.
--
-- This module has no new postulate, no synthetic complex carrier and
-- NO claim of eta compact-uniform convergence or RH. Pinned Agda
-- kernel/type checking of this source-written term still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- The original eta blocks are sums in the original Bishop complex
-- carrier. No change in sign convention or zero/one-based indexing.
originalShiftedEtaPairs :
  (Nat → BC.BishopComplex) → Nat → Nat → BC.BishopComplex
originalShiftedEtaPairs term n zero = BC.zeroC
originalShiftedEtaPairs term n (suc m) =
  BC._+C_
    (originalShiftedEtaPairs term n m)
    (Eta.originalEtaBlock term (n + m))

bishopComplexAddRightZero :
  (x : BC.BishopComplex) →
  Eta._≈C_ x (BC._+C_ x BC.zeroC)
bishopComplexAddRightZero (BC.bishop-complex xr xi) =
  (let open RP.ℝ-Solver in
   solve 1 (λ a → a ⊜ (a ⊕ Κ 0ℚᵘ)) RP.≃-refl xr)
  ,
  (let open RP.ℝ-Solver in
   solve 1 (λ a → a ⊜ (a ⊕ Κ 0ℚᵘ)) RP.≃-refl xi)

bishopComplexAddAssoc :
  (a b c : BC.BishopComplex) →
  Eta._≈C_
    (BC._+C_ (BC._+C_ a b) c)
    (BC._+C_ a (BC._+C_ b c))
bishopComplexAddAssoc
  (BC.bishop-complex ar ai)
  (BC.bishop-complex br bi)
  (BC.bishop-complex cr ci) =
  (let open RP.ℝ-Solver in
   solve 3
     (λ x y z → (x ⊕ y) ⊕ z ⊜ x ⊕ (y ⊕ z))
     RP.≃-refl ar br cr)
  ,
  (let open RP.ℝ-Solver in
   solve 3
     (λ x y z → (x ⊕ y) ⊕ z ⊜ x ⊕ (y ⊕ z))
     RP.≃-refl ai bi ci)

-- Source-native shifted cumulative tail, ALL n,m, including n=0
-- and m=0. The proof's only index rewrites are Nat addition.
originalBishopEtaPrefixShiftedPairsExact :
  (term : Nat → BC.BishopComplex) →
  (n m : Nat) →
  Eta._≈C_
    (Eta.originalEtaPrefix term (n + m))
    (BC._+C_
      (Eta.originalEtaPrefix term n)
      (originalShiftedEtaPairs term n m))
originalBishopEtaPrefixShiftedPairsExact term n zero
  rewrite NatP.+-identityʳ n =
  bishopComplexAddRightZero (Eta.originalEtaPrefix term n)
originalBishopEtaPrefixShiftedPairsExact term n (suc m)
  rewrite NatP.+-suc n m =
  Eta.≈C-trans
    (Eta.addRightCongruent
      (originalBishopEtaPrefixShiftedPairsExact term n m)
      (Eta.originalEtaBlock term (n + m)))
    (bishopComplexAddAssoc
      (Eta.originalEtaPrefix term n)
      (originalShiftedEtaPairs term n m)
      (Eta.originalEtaBlock term (n + m)))

module OriginalRound11 (inputs : Round11.Round11BishopCutset) where
  module Selected = Eta.OriginalRound11DirichletEta inputs

  -- The original selected Round11 source, not just an arbitrary term.
  actualOriginalRound11ShiftedEtaTailExact :
    (s : BC.BishopComplex) (n m : Nat) →
    Eta._≈C_
      (Eta.originalEtaPrefix (Selected.sourceTerms s) (n + m))
      (BC._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (originalShiftedEtaPairs (Selected.sourceTerms s) n m))
  actualOriginalRound11ShiftedEtaTailExact s n m =
    originalBishopEtaPrefixShiftedPairsExact
      (Selected.sourceTerms s) n m
