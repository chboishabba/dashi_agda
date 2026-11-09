{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopRiemannOriginalZetaAboveTwoExact where

------------------------------------------------------------------------
-- Genuine native Bishop zeta construction in the region Re(s)>2.
--
-- This module uses the literal original complex Dirichlet terms
--   expC (-s * sourceCanonicalNatLogCandidate n)
-- and the existing all-index Basel majorant, which is derived from
-- ONE original LOG inversion identity and the source Round11 signed
-- factorial product. Its value is the actual Bishop Sequence limit,
-- not a selected function field of the opaque RiemannAnalyticSubstrate.
--
-- P2 split (mathematically essential):
--   (a) source-native holomorphic-region VALUE construction: this file;
--   (b) genuine analytic continuation / original externally selected
--       zeta-function identification: NOT deduced here.
--
-- Cauchy/Riemann/Dirichlet; Bishop-Bridges; Murray/Csimma pinned
-- Bishop Real/Sequence; DASHI original Basel and Round11 owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.Nat.Base as Nat
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as R
import Sequence as Seq

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact as AboveTwo
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Uniform
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as NativeLog
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

module FromOriginalNegativeLog
  (inputs : Round11.Round11BishopCutset)
  (originalLogIdentity : NativeLog.OriginalBishopNegativeLogExponentialGap)
  where

  sourceTerms : Dirichlet.BishopDirichletTermFamily
  sourceTerms =
    Terms.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate

  sourceRegion : BC.BishopComplex → Set
  sourceRegion = AboveTwo.sourceAboveTwoRegion

  sourceBound : Uniform.RegionBaselDomination sourceTerms sourceRegion
  sourceBound =
    Native.sourceRegionBaselFromOneNativeLogIdentity
      inputs originalLogIdentity

  -- A dependent-domain original analytic VALUE rather than an opaque
  -- globally-extended zeta. It is literally the two original Seq.lim
  -- coordinates of expC(-s*log(n+1)).
  originalZetaAboveTwo :
    (s : BC.BishopComplex) → sourceRegion s → BC.BishopComplex
  originalZetaAboveTwo s aboveTwo =
    Uniform.regionDirichletValue
      sourceTerms sourceRegion sourceBound s aboveTwo

  -- The exact original Bishop Dirichlet finite partial sums.
  originalZetaPartial :
    BC.BishopComplex → Nat → BC.BishopComplex
  originalZetaPartial = Dirichlet.dirichletPartial sourceTerms

  -- This certifies both original coordinate limits directly, with
  -- no chosen analytic-function Set field or same-object oracle.
  originalZetaIsSourceDirichletLimit :
    (s : BC.BishopComplex) →
    (aboveTwo : sourceRegion s) →
    (Seq._ConvergesTo_
      (λ n → BC.re (originalZetaPartial s n))
      (BC.re (originalZetaAboveTwo s aboveTwo)))
    ×
    (Seq._ConvergesTo_
      (λ n → BC.im (originalZetaPartial s n))
      (BC.im (originalZetaAboveTwo s aboveTwo)))
  originalZetaIsSourceDirichletLimit s aboveTwo =
    Uniform.regionValueConvergesCoordinatewise
      sourceTerms sourceRegion sourceBound s aboveTwo

  -- An explicit, uniform modulus on the WHOLE Re(s)>2 region.
  -- No s-specific convergence cutoff is reselected.
  originalZetaUniformApproximation :
    (k : Nat) → .{{_ : Nat.NonZero k}} →
    (s : BC.BishopComplex) →
    (aboveTwo : sourceRegion s) →
    (m : Nat) →
    m Nat.≥ Uniform.baselUniformTailCutoff k →
    (R._≤_
      (R.∣ R._-_
        (BC.re (originalZetaAboveTwo s aboveTwo))
        (BC.re (originalZetaPartial s m)) ∣)
      (R._⋆ (+ 1 / k)))
    ×
    (R._≤_
      (R.∣ R._-_
        (BC.im (originalZetaAboveTwo s aboveTwo))
        (BC.im (originalZetaPartial s m)) ∣)
      (R._⋆ (+ 1 / k)))
  originalZetaUniformApproximation k s aboveTwo m mPast =
    Uniform.regionRealUniformLimitError
      sourceTerms sourceRegion sourceBound k s aboveTwo m mPast
    ,
    Uniform.regionImagUniformLimitError
      sourceTerms sourceRegion sourceBound k s aboveTwo m mPast

  -- The original convergence value is independent of any SECOND
  -- legitimate Basel majorant receipt; source terms decide it.
  originalZetaIndependentOfMajorant :
    (s : BC.BishopComplex) →
    (aboveTwo : sourceRegion s) →
    (other : Dirichlet.BishopDirichletBaselMajorantAt sourceTerms s) →
    (R._≃_
      (BC.re (originalZetaAboveTwo s aboveTwo))
      (BC.re (Dirichlet.dirichletValue sourceTerms s other)))
    ×
    (R._≃_
      (BC.im (originalZetaAboveTwo s aboveTwo))
      (BC.im (Dirichlet.dirichletValue sourceTerms s other)))
  originalZetaIndependentOfMajorant s aboveTwo other =
    Dirichlet.dirichletValueIndependentOfMajorant
      sourceTerms s
      (Uniform.regionPointwiseMajorant
        sourceTerms sourceRegion sourceBound s aboveTwo)
      other
