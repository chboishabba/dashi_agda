module DASHI.Physics.Closure.NSTriadKNSpectatorNestedOuterGramGluingBidiExact where

------------------------------------------------------------------------
-- SELECTED SPECTATOR NESTED OUTER FOLD -> EXACT SIGNED GRAM GLUING
--
-- Graph-colouring cross-pollination, used only as proof-search discipline:
-- a local recolouring/orbit quotient is not globally admissible merely because
-- it is valid on each local piece; it must survive the actual seam/gluing
-- consumer.  The NS analogue is that the inner LH <-> HL quotient does not by
-- itself control the outer spectator-weighted fold.
--
-- R573 already gives the literal selected outer cell
--
--   G_beta(alpha) = w_beta(alpha) * i * nestedSlotFold(alpha)
--
-- with the p_alpha = 0 branch kept exactly zero.  R180 owns the exact finite
-- Gram telescope on any C^3 list.  This owner composes those two facts only:
--
--   ||sum_alpha G_beta(alpha)||^2
--     = sum_alpha ||G_beta(alpha)||^2 + outerGramDebt_beta.
--
-- No absolute value, cardinality bound, arbitrary-coefficient operator norm,
-- or spacetime estimate is inserted.  Hence the live outer seam is exposed as
-- a SELECTED signed Gram debt rather than silently replaced by a stronger
-- R473 all-coefficients obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as Weld

F : C3.RealField _
F = Rational.rationalRealField

module OuterGluing
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module SN = Weld.SpectatorNested physicalSystem S L H velocityTransverse

  module AtSpectator (beta : Physical.PhysicalTriadIncidence) where
    module N = SN.Nested beta

    outerCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
    outerCell = N.nestedWeightedCompanionCell

    outerCells :
      List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
    outerCells = map outerCell

    sumCellsIsOuterFold :
      (items : List Physical.PhysicalTriadIncidence) →
      R180.sumCells (outerCells items)
      ≡ R224.foldVector outerCell items
    sumCellsIsOuterFold [] = refl
    sumCellsIsOuterFold (alpha ∷ rest) =
      cong (C3.complex3Add (outerCell alpha))
        (sumCellsIsOuterFold rest)

    exactSelectedOuterGramLedger :
      (items : List Physical.PhysicalTriadIncidence) →
      L2.complex3NormSquared (R224.foldVector outerCell items)
      ≡ R180.cellMassSum (outerCells items)
        + R180.gramDebt (outerCells items)
    exactSelectedOuterGramLedger items =
      trans
        (cong L2.complex3NormSquared
          (symEq (sumCellsIsOuterFold items)))
        (R180.finiteFibreGramLedger (outerCells items))
      where
      symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
      symEq refl = refl

------------------------------------------------------------------------
-- Status / graph-colouring-inspired gluing firewall.
------------------------------------------------------------------------

innerLHHLOrbitQuotientAutomaticallyPaysOuterGluing : Bool
innerLHHLOrbitQuotientAutomaticallyPaysOuterGluing = false

selectedOuterGramLedgerClosed : Bool
selectedOuterGramLedgerClosed = true

arbitraryCoefficientGramOperatorRequiredHere : Bool
arbitraryCoefficientGramOperatorRequiredHere = false

selectedOuterSignedGramDebtPaid : Bool
selectedOuterSignedGramDebtPaid = false

cutoffUniformOuterSpacetimeBoundPaid : Bool
cutoffUniformOuterSpacetimeBoundPaid = false

clayPromotion : Bool
clayPromotion = false
