{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySUNLiteralProbeWilsonNormalizationExact where

------------------------------------------------------------------------
-- LITERAL WILSON PROBE -> SIGNED CMP119 COEFFICIENT
--
-- This reuses the YM #1049 actual SU(N) Wilson link/plaquette action,
-- not an independently chosen two-coordinate localized-action model.
--
--  S[U] = u W+[U]                 (positive Wilson cost)
-- -S[U] = (-u) W+[U]              (Gibbs exponent / log density)
--  S[U] = (-u) W-[U], W- = -W+    (negative oriented basis)
--
-- A selected CMP119 source whose exponent's Wilson sector evaluates to
-- c_k W+[U*] on a nonzero literal plaquette probe U* must have c_k = -u_k,
-- provided its exponent equals the NEGATIVE literal finite Wilson action
-- at that probe.  The normalization proof cancels an actual positive Wilson
-- plaquette value; it does NOT assume (-c_k)g_k^2 = 1 or c_k = -u_k.
--
-- Remaining physics is to identify the published selected source's Wilson
-- density exponent at U* and its finite inverse-square coupling with these
-- concrete SU(N) objects. Do not treat the probe comparison as already paid.
--
-- Sources: Wilson, Phys. Rev. D 10 (1974), 2445--2459,
-- DOI 10.1103/PhysRevD.10.2445.
-- Dashen--Gross, Phys. Rev. D 23 (1981), 2340--2348,
-- DOI 10.1103/PhysRevD.23.2340.
-- Bałaban, Commun. Math. Phys. 119 (1988), 243--285,
-- DOI 10.1007/BF01217741, Sect. 2.
-- DASHI contribution: literal-to-CMP119 probe cancellation and the
-- explicit action-versus-density-exponent orientation firewall.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; Positive; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieLatticeGauge using
  (GaugeField)
open import DASHI.Physics.YangMills.SUNMatrixCarrier using
  (CertifiedSUNMatrixTheory; SUNMatrixElement)
import DASHI.Physics.YangMills.SUNWilsonAction as Wilson
import DASHI.Physics.YangMills.BalabanClayT4SUNWilsonActionConventionExact as Literal
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact as Cancel
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as CMP109

module _
  {N : Nat}
  {Matrix Complex Vertex : Set}
  {theory : CertifiedSUNMatrixTheory N Matrix Complex}
  {Edge : Vertex → Vertex → Set}
  (action : Literal.ScaledSUNWilsonActionData
    {Scalar = ℚ} theory Edge)
  where

  positiveCost :
    GaugeField {G = SUNMatrixElement theory} Edge → ℚ
  positiveCost field =
    Wilson.sunWilsonAction (Literal.wilsonData action) field

  negativeCost :
    GaugeField {G = SUNMatrixElement theory} Edge → ℚ
  negativeCost field = - positiveCost field

  inverseSquare : ℚ
  inverseSquare = Literal.inverseCouplingSq action

  -- In the source literal SU(N) action, 'multiply' is still a selected
  -- Scalar operation. Identifying it with rational multiplication is
  -- necessary to compare with the CMP109 rational coupling.
  module _
    (literalMultiplication : ∀ x y →
      Literal.multiply action x y ≡ x * y)
    where

    literalWilsonActionPositiveBasis :
      ∀ field →
      Literal.scaledWilsonAction action field
      ≡ inverseSquare * positiveCost field
    literalWilsonActionPositiveBasis field =
      trans
        (Literal.scaledWilsonActionDefinition action field)
        (literalMultiplication inverseSquare (positiveCost field))

    literalGibbsExponentNegativeCoefficient :
      ∀ field →
      - Literal.scaledWilsonAction action field
      ≡ (- inverseSquare) * positiveCost field
    literalGibbsExponentNegativeCoefficient field =
      trans
        (cong -_ (literalWilsonActionPositiveBasis field))
        (Ring.solve-∀ inverseSquare (positiveCost field))

    literalWilsonActionNegativeCostBasis :
      ∀ field →
      Literal.scaledWilsonAction action field
      ≡ (- inverseSquare) * negativeCost field
    literalWilsonActionNegativeCostBasis field =
      trans
        (literalWilsonActionPositiveBasis field)
        (Ring.solve-∀ inverseSquare (positiveCost field))

    -- The probe must be an ACTUAL Wilson field with strictly positive cost.
    -- The physical source obligation is now ONE equality of the selected
    -- density's Wilson exponent with the literal exp(-S) at that field.
    selectedExponentProbeDeterminesCoefficient :
      (field : GaugeField {G = SUNMatrixElement theory} Edge) →
      Positive (positiveCost field) →
      (coefficient : ℚ) →
      coefficient * positiveCost field
        ≡ - Literal.scaledWilsonAction action field →
      coefficient ≡ - inverseSquare
    selectedExponentProbeDeterminesCoefficient field positive coefficient probe =
      Cancel.cancelPositiveRightProduct
        coefficient (- inverseSquare) (positiveCost field) positive
        (trans probe (literalGibbsExponentNegativeCoefficient field))

    module _
      {Density Background Fluctuation
       Action WilsonTerm E R B Vacuum : Set}
      (source : CMP119.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm E R B Vacuum)
      (trajectory : CMP109.SourceNormalizedCouplingTrajectory)
      (scale : Nat)
      (literalInverseSameCMP109Node :
        inverseSquare ≡ CMP109.inverseCoupling trajectory scale)
      where

      selectedSourceExponentProbeDeterminesCMP109Wilson :
        (field : GaugeField {G = SUNMatrixElement theory} Edge) →
        Positive (positiveCost field) →
        CMP119.wilsonCoefficient source scale * positiveCost field
          ≡ - Literal.scaledWilsonAction action field →
        CMP119.wilsonCoefficient source scale
          ≡ - CMP109.inverseCoupling trajectory scale
      selectedSourceExponentProbeDeterminesCMP109Wilson field positive sourceProbe =
        trans
          (selectedExponentProbeDeterminesCoefficient
            field positive (CMP119.wilsonCoefficient source scale) sourceProbe)
          (cong -_ literalInverseSameCMP109Node)
