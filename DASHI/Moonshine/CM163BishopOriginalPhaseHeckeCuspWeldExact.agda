module DASHI.Moonshine.CM163BishopOriginalPhaseHeckeCuspWeldExact where

-- ORIGINAL PAPER 9 COARSE CLOSED SOURCE CONE (kernel pending).
--
-- Same Round11 Bishop cutset is threaded through the original:
-- (i) completed Machin arctan/clipped-mesh phase at ACTUAL CM tau,
-- (ii) actual Hecke diagonal and slice polynomial residual,
-- (iii) source S/T invariance, uniform original cusp bound and
--      original Bishop zero-limit along the SAME chosen cusp path.
--
-- There is no assertion that cusp zero + modular invariance implies
-- a global identity: modular invariant 1/j is a counterexample
-- without a pole-free holomorphic hypothesis.
--
-- The remaining genuinely GLOBAL modular-rigidity proof must show
-- the actual Hecke residual is pole-free holomorphic on the relevant
-- compactified modular quotient, with the original cusp extension,
-- before promoting the local limit to an all-domain identity.
-- Likewise, a record of pointwise coefficients does not automatically
-- construct the needed diagonal/slice finite integer gates.

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Tail
import DASHI.Moonshine.CM163BishopHecke41CuspLimitExact as Cusp
import DASHI.Moonshine.CM163BishopSelectedTauExponentExact as Phase
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

module Original (inputs : Round11.BishopCutset) where

  module H = Cusp.At inputs
  module Residual = H.R0
  module Bound = H.B
  module SourcePhase = Phase.FromOriginalBishopEndpoint inputs

  -- Already paid on the ORIGINAL selected negative-real q.
  actualCMPhase :
    C._≈C_ SourcePhase.Actual.actualBishopExpQ CM.q
  actualCMPhase = SourcePhase.actualOriginalCMQ

  selectedDeltaNegative :
    R._<_ CM.Selected.d R.0ℝ
  selectedDeltaNegative = Tail.negativeDelta

  selectedE4Positive : R.Positive CM.Selected.X
  selectedE4Positive = Tail.xPositive

  selectedE6Positive : R.Positive CM.Selected.Y
  selectedE6Positive = Tail.yPositive

  -- No fresh analytic-series surrogate or new product: the equality
  -- predicates are those of the existing original Hecke source.
  record CuspSourceGates : Set where
    field
      unit : Residual.R.W.UnitGate
      diagonal : Residual.R.W.DiagonalGate
      slice : Residual.R.W.SliceGate

  record ActualCuspRay : Set where
    field
      ray : Nat → U.BishopUpperHalfPlanePoint
      inside : (n : Nat) →
        R._≤_ (Norm.normSqC (Residual.t (ray n)))
          (Norm.normSqC Bound.reference)
      phaseNull :
        Lim.Conv (λ n → Residual.t (ray n)) A.zeroC

  module At (gates : CuspSourceGates) (cusp : ActualCuspRay) where
    open CuspSourceGates gates
    open ActualCuspRay cusp

    -- Both actual polynomial residuals vanish along the SAME ray,
    -- using all-index coefficient tails and the existing bounded disk.
    diagonalCuspZero :
      Lim.Conv (λ n → Residual.d (ray n)) A.zeroC
    diagonalCuspZero =
      H.diagonalZeroAlong unit diagonal ray inside phaseNull

    sliceCuspZero :
      Lim.Conv (λ n → Residual.s (ray n)) A.zeroC
    sliceCuspZero =
      H.sliceZeroAlong unit slice ray inside phaseNull

    -- Source modular invariance is ALREADY constructed. Reusing
    -- these proofs here does not assume the unproved rigidity theorem.
    diagonalInvariantS : ∀ p →
      C._≈C_
        (Residual.d (Gen.actS p))
        (Residual.d p)
    diagonalInvariantS = Residual.dS

    diagonalInvariantT : ∀ p →
      C._≈C_
        (Residual.d (Gen.actT p))
        (Residual.d p)
    diagonalInvariantT = Residual.dT

    sliceInvariantS : ∀ p →
      C._≈C_
        (Residual.s (Gen.actS p))
        (Residual.s p)
    sliceInvariantS = Residual.sS

    sliceInvariantT : ∀ p →
      C._≈C_
        (Residual.s (Gen.actT p))
        (Residual.s p)
    sliceInvariantT = Residual.sT

    -- The unfinished GLOBAL theorem is explicitly not fabricated:
    -- show the original residuals are holomorphic/pole-free over the
    -- compactified modular quotient; constructive rigidity turns
    -- the cusp limit into all-point diagonal/slice identities.
    -- That would then supply the existing actual CM root/Hecke
    -- signed reciprocal two-jet consumers without redefining j or π.
