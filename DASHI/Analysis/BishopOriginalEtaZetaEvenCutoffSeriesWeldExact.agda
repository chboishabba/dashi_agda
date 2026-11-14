module DASHI.Analysis.BishopOriginalEtaZetaEvenCutoffSeriesWeldExact where

------------------------------------------------------------------------
-- P2: SAME-OBJECT finite cutoff weld for ORIGINAL Bishop eta/zeta.
--
-- The earlier originalBishopEtaZetaPairing uses consecutive PAIRS of
-- the actual source exponential Dirichlet terms. The pinned native
-- Bishop Sequence.SeriesOf and Dirichlet.dirichletPartial use the
-- natural-number prefix count. This module proves, for ALL terms
-- and ALL cutoffs, that the paired prefix is EXACTLY the original
-- native source Dirichlet partial sum at count 2*N.
--
-- No phantom new zeta function, complex quotient, integrals,
-- continuation, eta denominator division or extra axiom.
-- All equality is in original Bishop REAL setoid coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.Nat.Properties as NatP

import RealProperties as RP
import Sequence as Sequence

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Actual finite prefix, with the same terms and cutoff convention as
-- the vendored Bishop Sequence.SeriesOf.
originalBishopPrefixIsNativeSeries :
  (term : Nat → BC.BishopComplex) →
  (n : Nat) →
  Eta._≈C_
    (Eta.originalBishopPrefix term n)
    (BC.bishop-complex
      (Sequence.SeriesOf (λ k → BC.re (term k)) n)
      (Sequence.SeriesOf (λ k → BC.im (term k)) n))
originalBishopPrefixIsNativeSeries term zero =
  RP.≃-refl , RP.≃-refl
originalBishopPrefixIsNativeSeries term (suc n) =
  RP.+-cong
    (proj₁ (originalBishopPrefixIsNativeSeries term n))
    RP.≃-refl
  ,
  RP.+-cong
    (proj₂ (originalBishopPrefixIsNativeSeries term n))
    RP.≃-refl

-- IMPORTANT: in the native Nat addition (n+n),
-- 2*(n+1) is not always definitionally 2*n+2.
twoIndexSuccessor :
  (n : Nat) →
  Eta.twice (suc n) ≡ suc (suc (Eta.twice n))
twoIndexSuccessor n = cong suc (NatP.+-suc n n)

originalBishopAdditionReassociate :
  (left middle right : BC.BishopComplex) →
  Eta._≈C_
    (BC._+C_ left (BC._+C_ middle right))
    (BC._+C_ (BC._+C_ left middle) right)
originalBishopAdditionReassociate
    (BC.bishop-complex ar ai)
    (BC.bishop-complex br bi)
    (BC.bishop-complex cr ci) =
  (let open RP.ℝ-Solver in
   solve 3
     (λ a b c → a ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c)
     RP.≃-refl ar br cr)
  ,
  (let open RP.ℝ-Solver in
   solve 3
     (λ a b c → a ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c)
     RP.≃-refl ai bi ci)

-- A genuine block-reindexing theorem for the ACTUAL source
-- Bishop Cartesian complex (not Q[i] and not a fresh series).
pairedUnsignedIsOriginalEvenPrefix :
  (term : Nat → BC.BishopComplex) →
  (n : Nat) →
  Eta._≈C_
    (Eta.originalZetaPrefix term n)
    (Eta.originalBishopPrefix term (Eta.twice n))
pairedUnsignedIsOriginalEvenPrefix term zero =
  RP.≃-refl , RP.≃-refl
pairedUnsignedIsOriginalEvenPrefix term (suc n)
  rewrite twoIndexSuccessor n =
  Eta.≈C-trans
    (Eta.addRightCongruent
      (pairedUnsignedIsOriginalEvenPrefix term n)
      (Eta.originalUnsignedBlock term n))
    (originalBishopAdditionReassociate
      (Eta.originalBishopPrefix term (Eta.twice n))
      (term (Eta.twice n))
      (term (suc (Eta.twice n))))

-- This is the previously unpaid true SAME-OBJECT P2 weld:
-- the finite zeta value from the paired eta proof is literally
-- the original Dirichlet partial sum at 2*N.
pairedUnsignedIsOriginalDirichletPartial :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (s : BC.BishopComplex) →
  (n : Nat) →
  Eta._≈C_
    (Eta.originalZetaPrefix (terms s) n)
    (Dirichlet.dirichletPartial terms s (Eta.twice n))
pairedUnsignedIsOriginalDirichletPartial terms s n =
  Eta.≈C-trans
    (pairedUnsignedIsOriginalEvenPrefix (terms s) n)
    (originalBishopPrefixIsNativeSeries
      (terms s) (Eta.twice n))

-- This is the single all-cutoff ORIGINAL SOURCE consumer:
-- finite eta plus two even-indexed source terms IS the actual
-- Dirichlet SeriesOf partial at 2*N. It does not assert any
-- analytic limit, division by the eta factor, or continuation.
originalEtaAndEvenTermsIsNativeZetaPartial :
  (terms : Dirichlet.BishopDirichletTermFamily) →
  (s : BC.BishopComplex) →
  (n : Nat) →
  Eta._≈C_
    (BC._+C_
      (Eta.originalEtaPrefix (terms s) n)
      (BC._+C_
        (Eta.originalEvenPositivePrefix (terms s) n)
        (Eta.originalEvenPositivePrefix (terms s) n)))
    (Dirichlet.dirichletPartial terms s (Eta.twice n))
originalEtaAndEvenTermsIsNativeZetaPartial terms s n =
  Eta.≈C-trans
    (Eta.originalBishopEtaZetaPairing (terms s) n)
    (pairedUnsignedIsOriginalDirichletPartial terms s n)

-- Reuse the actual original Round11 native-exponential Dirichlet
-- term family (whose chosen negative-log source remains genuine).
module OriginalRound11
  (inputs : Round11.Round11BishopCutset)
  where

  module Selected = Eta.OriginalRound11DirichletEta inputs

  actualRound11PairedZetaIsNativeSeries :
    (s : BC.BishopComplex) →
    (n : Nat) →
    Eta._≈C_
      (Eta.originalZetaPrefix (Selected.sourceTerms s) n)
      (Dirichlet.dirichletPartial Selected.sourceTerms s
        (Eta.twice n))
  actualRound11PairedZetaIsNativeSeries =
    pairedUnsignedIsOriginalDirichletPartial Selected.sourceTerms

  -- No separate zeta carrier: concrete source eta + even terms
  -- agrees with the true original Round11 Dirichlet partial sum.
  actualRound11EtaIsNativeZetaAtEvenCutoff :
    (s : BC.BishopComplex) →
    (n : Nat) →
    Eta._≈C_
      (BC._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (BC._+C_
          (Eta.originalEvenPositivePrefix (Selected.sourceTerms s) n)
          (Eta.originalEvenPositivePrefix (Selected.sourceTerms s) n)))
      (Dirichlet.dirichletPartial Selected.sourceTerms s
        (Eta.twice n))
  actualRound11EtaIsNativeZetaAtEvenCutoff =
    originalEtaAndEvenTermsIsNativeZetaPartial Selected.sourceTerms

-- Exact remaining analytic P2:
--  * source even-term rescaling log(2n)=log(2)+log(n);
--  * a source-native eta convergence modulus on compact s-domains;
--  * conditional eta quotient only away from all complex factor
--    zeros, including nonzero imaginary translates of s=1;
--  * removable-singularity and unique continuation witnesses;
--  * selected analytic-function-layer same-value identification.
-- There is no analytic completion or odd-zeta irrationality here.
