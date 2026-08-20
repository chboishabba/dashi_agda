module DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND98 / NORMALIZATION AUDIT FOR THE PACKET-LOG WELD
--
-- Round96's packet object is deliberately built from the *three energy legs*
-- of each physical incidence, and each leg uses `orderedPairPower`, i.e. the
-- symmetrized (p,q)+(q,p) power.  By contrast Round39 proves that the actual
-- projected Galerkin convection/energy pairing is the raw ordered-incidence
-- fold, with no hidden factor two.
--
-- Round38 already proves on the complete physical enumeration that
--
--   three-leg ordered-pair fold = 6 * ordered projected fold.
--
-- Therefore it is NOT legitimate to identify Round96's raw
-- `sumBoundaryTransfer` definitionally with the PDE boundary flux.  The
-- selected/packet analogue must carry the same normalization audit.  This
-- module makes the only normalization compatible with the established global
-- convention explicit:
--
--   physicalBoundaryFlux := (1/6) * sumBoundaryTransfer.
--
-- The exact Round96 packet->boundary equality transports through that factor
-- immediately.  The remaining same-object theorem is now sharply reduced to
-- the selected weighted analogue of Round39's output-fibre partition: prove
-- that the actual selected projected pairing equals
-- `(1/6) * sumPacketTransfer`.  No sign/normalization freedom remains after
-- that theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact as Round96
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as Round39

F : C3.RealField _
F = Rational.rationalRealField

oneSixth : ℚ
oneSixth = Int.+ 1 / 6

normalizedPacketTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Nat → ℚ
normalizedPacketTransfer E I selected velocity cutoff =
  oneSixth *
    Round96.sumPacketTransfer E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)

normalizedBoundaryTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Nat → ℚ
normalizedBoundaryTransfer E I selected velocity cutoff =
  oneSixth *
    Round96.sumBoundaryTransfer E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)

normalizedLiteralPacketTransferIsBoundaryFlux :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (cutoff : Nat) →
  normalizedPacketTransfer E I selected velocity cutoff
    ≡ normalizedBoundaryTransfer E I selected velocity cutoff
normalizedLiteralPacketTransferIsBoundaryFlux
    E I selected velocity reality divergenceFree cutoff =
  cong (oneSixth *_)
    (Round96.literalCutoffPacketTransferIsBoundaryFlux
      E I selected velocity reality divergenceFree cutoff)

-- The established unweighted calibration.  This theorem is imported rather
-- than reproved so the normalization authority remains Round38 itself.
unweightedThreeLegCalibration :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Round38.literalThreeLegFoldIsSixOrderedFold E I velocity cutoff
    ≡ Round38.literalThreeLegFoldIsSixOrderedFold E I velocity cutoff
unweightedThreeLegCalibration E I velocity cutoff = refl

-- Round39 is the other authority boundary: the projected PDE convection
-- pairing is the ordered fold, not the three-leg/symmetrized fold.
actualProjectedConvectionUsesOrderedFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system :
    DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.FiniteComplex3GalerkinSystem
      F E I) →
  Round39.literalCutoffProjectedEnergyPairing system
    ≡ Round38.orderedFold E I
        (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.velocity system)
        (Physical.physicalTriadEnumeration
          (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.cutoff system))
actualProjectedConvectionUsesOrderedFold =
  Round39.literalConvectionPairingEqualsOrderedIncidenceFold

-- Status flags are intentionally fail-closed.  The normalization issue is
-- resolved; the selected weighted Round39 analogue still has to be proved
-- before the full physical packet PDE/log-reserve theorem can be declared.
round98RawRound96BoundaryFluxIsLiteralPDEFlux : Bool
round98RawRound96BoundaryFluxIsLiteralPDEFlux = false

round98NormalizedBoundaryFluxConventionFixed : Bool
round98NormalizedBoundaryFluxConventionFixed = true

round98SelectedWeightedOutputFiberIdentificationClosed : Bool
round98SelectedWeightedOutputFiberIdentificationClosed = false

round98NormalizedBoundaryFluxConventionFixedIsTrue :
  round98NormalizedBoundaryFluxConventionFixed ≡ true
round98NormalizedBoundaryFluxConventionFixedIsTrue = refl
