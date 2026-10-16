module DASHI.Moonshine.OggSSPClimbingGymBishopPhaseCellExact where

------------------------------------------------------------------------
-- BISHOP PHASE CELL -> NATIVE OGG WALL ADDRESS
--
-- This is the concrete setoid-real quantisation seam for the climbing gym.
-- Once an actual Bishop phase value is proved to lie strictly inside one
-- p^a cell, the existing generic Bishop cell compiler determines the same
-- native-p RadialTreeAddress used by the signed SSP wall.
--
-- This owner does NOT construct the phase x_p(t) itself.  In particular it
-- does not manufacture a global Bishop logarithm, a trigonometric-pi theorem,
-- or cell certificates for the numerical zeta ordinates.  Those are now the
-- remaining same-object analytic payments.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import Real as BishopReal

import DASHI.Analysis.BishopRadixCellQuantisationExact as BishopCell
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

WallRadixAddress : Gym.WallForm → Set
WallRadixAddress form =
  Radix.RadialTreeAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)

CertifiedWallPhaseCell :
  (form : Gym.WallForm) →
  BishopReal.ℝ →
  Set
CertifiedWallPhaseCell form phase =
  BishopCell.CertifiedOpenRadixCell
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)
    phase

certifiedWallPhaseAddress :
  (form : Gym.WallForm) →
  (phase : BishopReal.ℝ) →
  CertifiedWallPhaseCell form phase →
  WallRadixAddress form
certifiedWallPhaseAddress form phase certificate =
  BishopCell.certifiedRadialAddress certificate

certifiedWallPhaseIndex :
  (form : Gym.WallForm) →
  (phase : BishopReal.ℝ) →
  CertifiedWallPhaseCell form phase →
  Nat
certifiedWallPhaseIndex form phase certificate =
  BishopCell.cellIndex certificate

record BishopPhaseCellBoundary : Set where
  constructor bishop-phase-cell-boundary
  field
    concreteBishopCarrierUsed : Bool
    nativeOggRadixChartReused : Bool
    certifiedNonBoundaryPhaseCompiles : Bool
    totalRealFloorRequired : Bool

    globalBishopLogConstructedHere : Bool
    trigonometricPiConstructedHere : Bool
    actualZeroPhaseCellCertificatesConstructed : Bool
    phaseCellCertificateProvesZetaZero : Bool
    phaseCellCertificateProvesMonsterSpecificity : Bool

open BishopPhaseCellBoundary public

canonicalBishopPhaseCellBoundary : BishopPhaseCellBoundary
canonicalBishopPhaseCellBoundary =
  bishop-phase-cell-boundary
    true true true false
    false false false false false
