module DASHI.Moonshine.CM163BishopHecke41NormalizedEulerFlowExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- The cleared Euler equations for the actual normalized J=q*j.
-- Derive them from the original Ramanujan X^3 flow and reciprocal
-- discriminant-unit flow; no independent modular derivative premise.
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as E
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as Flow
open G
open F using (δ; dMul; dSub; dAdd; dCong)
open U using (X; Y; X2; X3)
open D using (Junit; reciprocal)

J1 J2 : Series
J1 = δ Junit
J2 = δ J1

-- The Euler operator for j=J/q is δ-1 on J.
L1 L2 : Series
L1 = J1 ⊖s Junit
L2 = (J2 ⊖s (J1 ⊕s J1)) ⊕s Junit

jFlow : J1 ≈s (Junit ⊖s ((X2 ⊗s Y) ⊗s reciprocal))
jFlow = transS (dMul X3 reciprocal)
  (transS (addCong (mulCong D.xFlow reflS) (mulCong reflS D.inverseFlow))
    (let open G.Solver in solve 4
      (λ e x y v →
        (e ⊗ (x ⊗ x ⊗ x) ⊖ (x ⊗ x) ⊗ y) ⊗ v
        ⊕ (x ⊗ x ⊗ x) ⊗ (⊝ ((e ⊖ Κ 1ℚᵘ) ⊗ v))
        ⊜ (x ⊗ x ⊗ x) ⊗ v ⊖ ((x ⊗ x) ⊗ y) ⊗ v)
      reflS E.E X Y reciprocal))

first : ((X ⊗s L1) ⊕s (Y ⊗s Junit)) ≈s H.zeroSeries
first = transS (addCong (mulCong reflS (subCong jFlow reflS)) reflS)
  (let open G.Solver in solve 3
    (λ x y v → x ⊗ (((x ⊗ x ⊗ x) ⊗ v ⊖ (x ⊗ x) ⊗ y ⊗ v) ⊖ (x ⊗ x ⊗ x) ⊗ v)
      ⊕ y ⊗ ((x ⊗ x ⊗ x) ⊗ v) ⊜ Κ 0ℚᵘ)
    reflS X Y reciprocal)

secondOperator : (δ L1 ⊖s L1) ≈s L2
secondOperator = transS (subCong (dSub J1 Junit) reflS)
  (let open G.Solver in solve 3 (λ a b c → (c ⊖ b) ⊖ (b ⊖ a) ⊜ (c ⊖ (b ⊕ b)) ⊕ a)
    reflS Junit J1 J2)

dFirst : δ ((X ⊗s L1) ⊕s (Y ⊗s Junit)) ≈s H.zeroSeries
dFirst = transS (dCong first) Flow.dZero

-- Apply δ-1 to the whole first residual, not a second independent
-- differential relation. Product rule leaves X L2 +(δX+Y)L1+δY J.
second : (((X ⊗s L2) ⊕s ((δ X ⊕s Y) ⊗s L1)) ⊕s (δ Y ⊗s Junit)) ≈s H.zeroSeries
second =
  let r = (X ⊗s L1) ⊕s (Y ⊗s Junit)
      expand = transS (dAdd (X ⊗s L1) (Y ⊗s Junit))
        (addCong (dMul X L1) (dMul Y Junit))
      zero = transS (subCong dFirst first)
        (let open G.Solver in solve 0 (Κ 0ℚᵘ ⊖ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) reflS)
      read = transS (subCong expand reflS)
        (let open G.Solver in solve 7
          (λ x y dx dy a b dl →
            ((dx ⊗ (b ⊖ a) ⊕ x ⊗ dl) ⊕ (dy ⊗ a ⊕ y ⊗ b))
              ⊖ (x ⊗ (b ⊖ a) ⊕ y ⊗ a)
            ⊜ (x ⊗ (dl ⊖ (b ⊖ a)) ⊕ (dx ⊕ y) ⊗ (b ⊖ a)) ⊕ dy ⊗ a)
          reflS X Y (δ X) (δ Y) Junit J1 (δ L1))
  in transS (symS (transS read
    (addCong (addCong (mulCong reflS secondOperator) reflS) reflS))) zero
