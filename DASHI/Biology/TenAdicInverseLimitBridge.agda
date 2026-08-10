module DASHI.Biology.TenAdicInverseLimitBridge where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Fernando Q. Gouvea, "p-adic Numbers: An Introduction", 2nd ed.,
-- Springer, 1997. DOI: 10.1007/978-3-642-59058-0.
--
-- CATEGORY-THEORY TERMINOLOGY
--
-- The inverse SYSTEM (the tower) represents a pro-object.  Its inverse limit,
-- when constructed in the ambient category, is a limit object; the limit
-- object itself should not be called the pro-object.
--
-- DASHI CONTRIBUTION
--
-- Prove the generic transport theorem needed by the decimal/CRT discussion.
-- A levelwise equivalence commuting with projection transports compatible
-- inverse-limit histories in both directions.  Product-tower histories split
-- exactly into a pair of histories and rejoin pointwise.  Consequently any
-- explicitly supplied coherent arithmetic CRT system promotes the decimal
-- residue history tower to the underlying 10-adic = 2-adic x 5-adic HISTORY
-- decomposition.  Ring operations remain a separate structure requirement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.StratifiedResolutionTowerExact as Tower
import DASHI.Biology.IndexedJStratifiedMultiresolutionExact as J
import DASHI.Biology.DecimalResidueTowerExact as Decimal
import DASHI.Biology.DecimalCRTResolutionExact as CRT

------------------------------------------------------------------------
-- Generic equivalence of inverse systems.
------------------------------------------------------------------------

record TowerEquivalence
  (A B : Tower.ResolutionTower) : Set₁ where
  constructor towerEquivalence
  field
    forward : (r : Nat) → Tower.ResolutionTower.Carrier A r →
      Tower.ResolutionTower.Carrier B r
    backward : (r : Nat) → Tower.ResolutionTower.Carrier B r →
      Tower.ResolutionTower.Carrier A r

    backwardForward :
      (r : Nat) (x : Tower.ResolutionTower.Carrier A r) →
      backward r (forward r x) ≡ x

    forwardBackward :
      (r : Nat) (x : Tower.ResolutionTower.Carrier B r) →
      forward r (backward r x) ≡ x

    forwardCommutes :
      ∀ {r} (x : Tower.ResolutionTower.Carrier A (suc r)) →
      Tower.ResolutionTower.project B (forward (suc r) x)
      ≡ forward r (Tower.ResolutionTower.project A x)

    backwardCommutes :
      ∀ {r} (x : Tower.ResolutionTower.Carrier B (suc r)) →
      Tower.ResolutionTower.project A (backward (suc r) x)
      ≡ backward r (Tower.ResolutionTower.project B x)

open TowerEquivalence public

mapForwardHistory :
  ∀ {A B} → TowerEquivalence A B →
  Tower.InverseLimitPoint A → Tower.InverseLimitPoint B
mapForwardHistory equivalence history =
  Tower.inverseLimitPoint
    (λ r → forward equivalence r (Tower.InverseLimitPoint.atResolution history r))
    (λ r →
      trans
        (forwardCommutes equivalence
          (Tower.InverseLimitPoint.atResolution history (suc r)))
        (cong (forward equivalence r)
          (Tower.InverseLimitPoint.coherent history r)))

mapBackwardHistory :
  ∀ {A B} → TowerEquivalence A B →
  Tower.InverseLimitPoint B → Tower.InverseLimitPoint A
mapBackwardHistory equivalence history =
  Tower.inverseLimitPoint
    (λ r → backward equivalence r (Tower.InverseLimitPoint.atResolution history r))
    (λ r →
      trans
        (backwardCommutes equivalence
          (Tower.InverseLimitPoint.atResolution history (suc r)))
        (cong (backward equivalence r)
          (Tower.InverseLimitPoint.coherent history r)))

forwardBackwardHistoryAt :
  ∀ {A B} (equivalence : TowerEquivalence A B)
    (history : Tower.InverseLimitPoint B) (r : Nat) →
  Tower.InverseLimitPoint.atResolution
    (mapForwardHistory equivalence (mapBackwardHistory equivalence history)) r
  ≡ Tower.InverseLimitPoint.atResolution history r
forwardBackwardHistoryAt equivalence history r =
  forwardBackward equivalence r
    (Tower.InverseLimitPoint.atResolution history r)

backwardForwardHistoryAt :
  ∀ {A B} (equivalence : TowerEquivalence A B)
    (history : Tower.InverseLimitPoint A) (r : Nat) →
  Tower.InverseLimitPoint.atResolution
    (mapBackwardHistory equivalence (mapForwardHistory equivalence history)) r
  ≡ Tower.InverseLimitPoint.atResolution history r
backwardForwardHistoryAt equivalence history r =
  backwardForward equivalence r
    (Tower.InverseLimitPoint.atResolution history r)

------------------------------------------------------------------------
-- Decimal address tower <-> canonical 10^r residue representative tower.
------------------------------------------------------------------------

residue10Tower : Tower.ResolutionTower
residue10Tower = record
  { Carrier = Decimal.Residue10
  ; project = Decimal.reduceResidue
  }

decodeReductionCompatible :
  ∀ {r} (x : Decimal.Residue10 (suc r)) →
  J.prefix (Decimal.decodeResidue x)
  ≡ Decimal.decodeResidue (Decimal.reduceResidue x)
decodeReductionCompatible {r} x =
  trans
    (sym
      (Decimal.decodeEncodeResidue
        (J.prefix (Decimal.decodeResidue x))))
    (cong Decimal.decodeResidue
      (trans
        (Decimal.encodePrefixCompatible (Decimal.decodeResidue x))
        (cong Decimal.reduceResidue (Decimal.encodeDecodeResidue x))))

decimalResidueTowerEquivalence :
  TowerEquivalence J.decimalResolutionTower residue10Tower
decimalResidueTowerEquivalence =
  towerEquivalence
    (λ r → Decimal.encodeResidue)
    (λ r → Decimal.decodeResidue)
    (λ r → Decimal.decodeEncodeResidue)
    (λ r → Decimal.encodeDecodeResidue)
    (λ x → sym (Decimal.encodePrefixCompatible x))
    decodeReductionCompatible

------------------------------------------------------------------------
-- The 2-adic/5-adic product tower and coherent CRT promotion.
------------------------------------------------------------------------

residue2Tower : Tower.ResolutionTower
residue2Tower = record
  { Carrier = CRT.Residue2
  ; project = CRT.reduceResidue 2
  }

residue5Tower : Tower.ResolutionTower
residue5Tower = record
  { Carrier = CRT.Residue5
  ; project = CRT.reduceResidue 5
  }

product25Tower : Tower.ResolutionTower
product25Tower = record
  { Carrier = CRT.ProductResidue25
  ; project = CRT.reduceProduct25
  }

crtTowerEquivalence :
  (system : CRT.CoherentCRTSystem) →
  TowerEquivalence residue10Tower product25Tower
crtTowerEquivalence system =
  towerEquivalence
    (λ r → CRT.crtForward (CRT.stage system r))
    (λ r → CRT.crtBackward (CRT.stage system r))
    (λ r → CRT.crtBackwardForward (CRT.stage system r))
    (λ r → CRT.crtForwardBackward (CRT.stage system r))
    (λ x → sym (CRT.forwardReductionCommutes system x))
    (λ x → sym (CRT.backwardReductionCommutes system x))

splitProductHistory :
  Tower.InverseLimitPoint product25Tower →
  Tower.InverseLimitPoint residue2Tower
  × Tower.InverseLimitPoint residue5Tower
splitProductHistory history =
  Tower.inverseLimitPoint
    (λ r → proj₁ (Tower.InverseLimitPoint.atResolution history r))
    (λ r → cong proj₁ (Tower.InverseLimitPoint.coherent history r))
  ,
  Tower.inverseLimitPoint
    (λ r → proj₂ (Tower.InverseLimitPoint.atResolution history r))
    (λ r → cong proj₂ (Tower.InverseLimitPoint.coherent history r))

joinProductHistories :
  Tower.InverseLimitPoint residue2Tower
  × Tower.InverseLimitPoint residue5Tower →
  Tower.InverseLimitPoint product25Tower
joinProductHistories (twoHistory , fiveHistory) =
  Tower.inverseLimitPoint
    (λ r →
      Tower.InverseLimitPoint.atResolution twoHistory r
      , Tower.InverseLimitPoint.atResolution fiveHistory r)
    (λ r →
      cong₂ _,_
        (Tower.InverseLimitPoint.coherent twoHistory r)
        (Tower.InverseLimitPoint.coherent fiveHistory r))

splitJoinProductAt :
  (histories :
    Tower.InverseLimitPoint residue2Tower
    × Tower.InverseLimitPoint residue5Tower)
  (r : Nat) →
  Tower.InverseLimitPoint.atResolution
    (proj₁ (splitProductHistory (joinProductHistories histories))) r
  ≡ Tower.InverseLimitPoint.atResolution (proj₁ histories) r
  ×
  Tower.InverseLimitPoint.atResolution
    (proj₂ (splitProductHistory (joinProductHistories histories))) r
  ≡ Tower.InverseLimitPoint.atResolution (proj₂ histories) r
splitJoinProductAt (twoHistory , fiveHistory) r = refl , refl

------------------------------------------------------------------------
-- End-to-end compatible-history maps.
------------------------------------------------------------------------

decimalHistoryToTwoFive :
  (system : CRT.CoherentCRTSystem) →
  Tower.InverseLimitPoint J.decimalResolutionTower →
  Tower.InverseLimitPoint residue2Tower
  × Tower.InverseLimitPoint residue5Tower
decimalHistoryToTwoFive system history =
  splitProductHistory
    (mapForwardHistory (crtTowerEquivalence system)
      (mapForwardHistory decimalResidueTowerEquivalence history))

twoFiveToDecimalHistory :
  (system : CRT.CoherentCRTSystem) →
  Tower.InverseLimitPoint residue2Tower
  × Tower.InverseLimitPoint residue5Tower →
  Tower.InverseLimitPoint J.decimalResolutionTower
twoFiveToDecimalHistory system histories =
  mapBackwardHistory decimalResidueTowerEquivalence
    (mapBackwardHistory (crtTowerEquivalence system)
      (joinProductHistories histories))

record TenAdicBridgeClaimScope : Set where
  constructor tenAdicBridgeClaimScope
  field
    genericInverseLimitTransportConstructed : Bool
    genericInverseLimitTransportConstructedIsTrue :
      genericInverseLimitTransportConstructed ≡ true

    productHistorySplittingConstructed : Bool
    productHistorySplittingConstructedIsTrue :
      productHistorySplittingConstructed ≡ true

    coherentCRTImpliesTwoFiveHistoryBridge : Bool
    coherentCRTImpliesTwoFiveHistoryBridgeIsTrue :
      coherentCRTImpliesTwoFiveHistoryBridge ≡ true

    fullProfiniteCompletionOfIntegersIdentifiedWithTenAdics : Bool
    fullProfiniteCompletionOfIntegersIdentifiedWithTenAdicsIsFalse :
      fullProfiniteCompletionOfIntegersIdentifiedWithTenAdics ≡ false

    inverseLimitRingOperationsConstructedHere : Bool
    inverseLimitRingOperationsConstructedHereIsFalse :
      inverseLimitRingOperationsConstructedHere ≡ false

canonicalTenAdicBridgeClaimScope : TenAdicBridgeClaimScope
canonicalTenAdicBridgeClaimScope =
  tenAdicBridgeClaimScope true refl true refl true refl false refl false refl
