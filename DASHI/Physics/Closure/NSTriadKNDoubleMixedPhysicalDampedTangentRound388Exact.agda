module DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact where

------------------------------------------------------------------------
-- ROUND388 / SAME-OBJECT DOUBLE-MIXED DAMPED TANGENT
--
-- R386 identifies the literal R378 Gram debt with the R180 debt of R225's
-- pointwise double-mixed cells.  R387 rewrites each such cell as
--
--   D_tau = 2 A_tau + 2 A_swap(tau),
--
-- where A is the literal R224 plus-minus mixed cell.  R382 already supplies
-- the exact physical damped-forced tangent for A_tau and A_swap(tau).
--
-- This module combines those two already-owned tangents.  Swap only exchanges
-- p and q, so its cell decay rate is unchanged by commutativity.  Therefore
-- the literal double-mixed carrier has the exact tangent
--
--   dD_tau = -rho_tau D_tau + G_tau,
--
-- where G_tau is exactly twice the R230 forcing at tau plus twice the R230
-- forcing at swap(tau).  No estimate, sign, integration, or new PDE identity
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairClosedRound382Exact as R382
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalDoubleMixed
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R382.ClosedLiteralPair physicalSystem S

  doubleTangent :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleTangent tau =
    C3.complex3Add
      (R387.doublePlus (Pair.mixedCellTangent tau))
      (R387.doublePlus
        (Pair.mixedCellTangent (Symmetry.swapTriad tau)))

  doubleForcing :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleForcing tau =
    C3.complex3Add
      (R387.doublePlus (Pair.mixedCellForcing tau))
      (R387.doublePlus
        (Pair.mixedCellForcing (Symmetry.swapTriad tau)))

  swappedCellRate :
    (tau : Physical.PhysicalTriadIncidence) →
    Pair.cellRate (Symmetry.swapTriad tau) ≡ Pair.cellRate tau
  swappedCellRate tau =
    solve
      (Pair.rho (Physical.p tau) ∷ Pair.rho (Physical.q tau) ∷ [])

  doubleMixedDampedTangent :
    (tau : Physical.PhysicalTriadIncidence) →
    doubleTangent tau
    ≡ C3.complex3Add
        (R291.realScale (0ℚ - Pair.cellRate tau)
          (R225.doubleMixedCell S Pair.velocity tau))
        (doubleForcing tau)
  doubleMixedDampedTangent tau
      rewrite Pair.mixedCellDampedLaw tau
            | Pair.mixedCellDampedLaw (Symmetry.swapTriad tau)
            | swappedCellRate tau
            | R387.doubleMixedIsSwapPairedPlusMinus S Pair.velocity tau =
    distribute
      (Pair.cellRate tau)
      (Pair.mixedCell tau)
      (Pair.mixedCell (Symmetry.swapTriad tau))
      (Pair.mixedCellForcing tau)
      (Pair.mixedCellForcing (Symmetry.swapTriad tau))
    where
    distribute :
      (rate : ℚ) (a b fa fb : C3.Complex3 F) →
      C3.complex3Add
        (R387.doublePlus
          (C3.complex3Add (R291.realScale (0ℚ - rate) a) fa))
        (R387.doublePlus
          (C3.complex3Add (R291.realScale (0ℚ - rate) b) fb))
      ≡ C3.complex3Add
          (R291.realScale (0ℚ - rate)
            (C3.complex3Add (R387.doublePlus a) (R387.doublePlus b)))
          (C3.complex3Add (R387.doublePlus fa) (R387.doublePlus fb))
    distribute rate
        (C3.complex3
          (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
        (C3.complex3
          (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi))
        (C3.complex3
          (C3.complex gar gai) (C3.complex gbr gbi) (C3.complex gcr gci))
        (C3.complex3
          (C3.complex hdr hdi) (C3.complex her hei) (C3.complex hfr hfi)) =
      let
        scalar = 0ℚ - rate
      in
      C3.complex3-ext
        (C3.complex-ext
          (solve (scalar ∷ ar ∷ dr ∷ gar ∷ hdr ∷ []))
          (solve (scalar ∷ ai ∷ di ∷ gai ∷ hdi ∷ [])))
        (C3.complex-ext
          (solve (scalar ∷ br ∷ er ∷ gbr ∷ her ∷ []))
          (solve (scalar ∷ bi ∷ ei ∷ gbi ∷ hei ∷ [])))
        (C3.complex-ext
          (solve (scalar ∷ cr ∷ fr ∷ gcr ∷ hfr ∷ []))
          (solve (scalar ∷ ci ∷ fi ∷ gci ∷ hfi ∷ [])))

round388LiteralDoubleMixedDampedTangentClosed : Bool
round388LiteralDoubleMixedDampedTangentClosed = true

round388SecondIndependentProjectorTangentNeeded : Bool
round388SecondIndependentProjectorTangentNeeded = false

round388TemporalIntegrationUsed : Bool
round388TemporalIntegrationUsed = false

round388LiteralDoubleMixedDampedTangentClosedIsTrue :
  round388LiteralDoubleMixedDampedTangentClosed ≡ true
round388LiteralDoubleMixedDampedTangentClosedIsTrue = refl
