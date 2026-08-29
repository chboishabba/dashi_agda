module DASHI.Physics.Closure.NSTriadKNCoherentGramOnlyCompanionCompilerRound220Exact where

------------------------------------------------------------------------
-- ROUND220 / CELL MASS PAID -> ONLY COHERENT GRAM RESIDUAL REMAINS
--
-- The exact Gram ledger is
--
--   ||sum cells||^2 = cellMass + gramDebt.
--
-- Round217/219 provide the no-cardinality route
--
--   cellMass <= 36 E D.
--
-- Therefore a coherent residual budget
--
--   gramDebt <= R_coh
--
-- immediately yields
--
--   ||sum cells||^2 <= 36 E D + R_coh.
--
-- This is the weakest backward-facing quartic companion socket after the
-- routine cell-mass payment.  It does not require Gram negativity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNRawCurlCellMassEnergyDissipationRound217Exact as R217

F = R180.F

record CoherentResidualCompanionPayment (cells : List (C3.Complex3 F)) : Set where
  constructor coherent-residual-companion-payment
  field
    energyDissipation coherentResidual : ℚ
    cellMassBound :
      R180.cellMassSum cells ≤ R217.thirtySix * energyDissipation
    coherentDebtBound :
      R180.gramDebt cells ≤ coherentResidual

open CoherentResidualCompanionPayment public

coherentResidualClosesCompanionMass :
  (cells : List (C3.Complex3 F)) →
  (payment : CoherentResidualCompanionPayment cells) →
  L2.complex3NormSquared (R180.sumCells cells)
  ≤ R217.thirtySix * energyDissipation payment
      + coherentResidual payment
coherentResidualClosesCompanionMass cells payment =
  let
    added :
      R180.cellMassSum cells + R180.gramDebt cells
      ≤ R217.thirtySix * energyDissipation payment
          + coherentResidual payment
    added = ℚP.+-mono-≤
      (cellMassBound payment)
      (coherentDebtBound payment)
  in
  subst
    (λ left →
      left
      ≤ R217.thirtySix * energyDissipation payment
          + coherentResidual payment)
    (R180.gramLedger cells)
    added

round220CellMassRemovedFromNovelFrontier : Bool
round220CellMassRemovedFromNovelFrontier = true

round220RequiresGramNegativity : Bool
round220RequiresGramNegativity = false

round220CoherentResidualIsOnlyCompanionLeaf : Bool
round220CoherentResidualIsOnlyCompanionLeaf = true

round220PhysicalCoherentGramResidualBudgetClosed : Bool
round220PhysicalCoherentGramResidualBudgetClosed = false

round220PackageAClosed : Bool
round220PackageAClosed = false

round220ClayPromotion : Bool
round220ClayPromotion = false

round220CellMassRemovedFromNovelFrontierIsTrue :
  round220CellMassRemovedFromNovelFrontier ≡ true
round220CellMassRemovedFromNovelFrontierIsTrue = refl

round220RequiresGramNegativityIsFalse :
  round220RequiresGramNegativity ≡ false
round220RequiresGramNegativityIsFalse = refl

round220CoherentResidualIsOnlyCompanionLeafIsTrue :
  round220CoherentResidualIsOnlyCompanionLeaf ≡ true
round220CoherentResidualIsOnlyCompanionLeafIsTrue = refl

round220PhysicalCoherentGramResidualBudgetClosedIsFalse :
  round220PhysicalCoherentGramResidualBudgetClosed ≡ false
round220PhysicalCoherentGramResidualBudgetClosedIsFalse = refl

round220PackageAClosedIsFalse : round220PackageAClosed ≡ false
round220PackageAClosedIsFalse = refl

round220ClayPromotionIsFalse : round220ClayPromotion ≡ false
round220ClayPromotionIsFalse = refl
