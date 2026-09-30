module DASHI.Physics.Foundations.CMP119LiteralWilsonProjectorSignAuditExact where

------------------------------------------------------------------------
-- Dashi-origin formal audit of TWO distinct Wilson plaquette orientations.
-- Primary source context:
-- K. G. Wilson, "Confinement of Quarks", Phys. Rev. D 10 (1974)
-- 2445--2459, DOI: 10.1103/PhysRevD.10.2445.
-- T. Balaban, "Convergent Renormalization Expansions for Lattice Gauge
-- Theories", Commun. Math. Phys. 119 (1988) 243--285,
-- DOI: 10.1007/BF01217741, Sect. 2, Eq. (2.23).
--
-- The canonical T4 plaquette basis has PROJECTOR VALUE +1.
-- The selected Wilson action written +u * (1 - half trace U_p) therefore
-- has projector +u, whereas -u * the same plaquette basis has projector -u.
-- This is a direct computation in the existing literal LocalizedAction
-- carrier, not a new source-normalization *assumption*.
--
-- Do not identify the positive-action coefficient with the negative
-- effective-density exponent coefficient until the actual source definition
-- supplies the exponential/sign conversion. Physical CMP119 source
-- identification, g^2 u = 1, and shell matching remain independently open.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

-- The actual T4 plaquette basis and its minus-sign exponent presentation.
positiveWilsonAction : ℚ → T4.LocalizedAction
positiveWilsonAction u =
  T4.scaleLocalizedAction u T4.plaquetteBasisAction

negativeWilsonExponent : ℚ → T4.LocalizedAction
negativeWilsonExponent u =
  T4.scaleLocalizedAction (- u) T4.plaquetteBasisAction

positiveWilsonCoefficientExact : ∀ u →
  T4.plaquetteCoefficientProjector (positiveWilsonAction u)
  ≡ u
positiveWilsonCoefficientExact u =
  trans
    (T4.plaquetteCoefficientHomogeneous u T4.plaquetteBasisAction)
    (trans
      (cong (u *_) T4.plaquetteCoefficientOfPlaquetteBasis)
      (ℚRing.solve-∀ u))

negativeWilsonCoefficientExact : ∀ u →
  T4.plaquetteCoefficientProjector (negativeWilsonExponent u)
  ≡ - u
negativeWilsonCoefficientExact u =
  trans
    (T4.plaquetteCoefficientHomogeneous (- u) T4.plaquetteBasisAction)
    (trans
      (cong ((- u) *_) T4.plaquetteCoefficientOfPlaquetteBasis)
      (ℚRing.solve-∀ u))

-- The source's complete effective action is not assumed to be *only* the
-- Wilson term. The four E/R/B/vacuum sectors remain separately projected.
positiveCanonicalNodeCoefficient :
  ∀ u e r b vacuum →
  T4.plaquetteCoefficientProjector
    (Canonical.canonicalAssemble
      u T4.plaquetteBasisAction e r b vacuum)
  ≡
  u +
    (T4.plaquetteCoefficientProjector e +
      (T4.plaquetteCoefficientProjector r +
        (T4.plaquetteCoefficientProjector b +
          T4.plaquetteCoefficientProjector vacuum)))
positiveCanonicalNodeCoefficient u e r b vacuum =
  ℚRing.solve-∀ u
    (T4.plaquetteCoefficientProjector e)
    (T4.plaquetteCoefficientProjector r)
    (T4.plaquetteCoefficientProjector b)
    (T4.plaquetteCoefficientProjector vacuum)

negativeCanonicalNodeCoefficient :
  ∀ u e r b vacuum →
  T4.plaquetteCoefficientProjector
    (Canonical.canonicalAssemble
      (- u) T4.plaquetteBasisAction e r b vacuum)
  ≡
  (- u) +
    (T4.plaquetteCoefficientProjector e +
      (T4.plaquetteCoefficientProjector r +
        (T4.plaquetteCoefficientProjector b +
          T4.plaquetteCoefficientProjector vacuum)))
negativeCanonicalNodeCoefficient u e r b vacuum =
  ℚRing.solve-∀ u
    (T4.plaquetteCoefficientProjector e)
    (T4.plaquetteCoefficientProjector r)
    (T4.plaquetteCoefficientProjector b)
    (T4.plaquetteCoefficientProjector vacuum)

-- A literal CMP119 native action has *a source-provided* coefficient c_k.
-- Without an established source-basis convention, even the same-action
-- algebra does NOT identify that source c_k with +/- inverse coupling.
-- This statement computes precisely what follows if the physical
-- source-action equality at k is obtained from the primary source.
module _
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  physicalSourceWilsonBasisPositive :
    ∀ k →
    CMP119.wilsonActionTerm source k
      ≡ T4.plaquetteBasisAction →
    T4.plaquetteCoefficientProjector
      (CMP119.wilsonActionTerm source k)
    ≡ 1ℚ
  physicalSourceWilsonBasisPositive k identity =
    trans
      (cong T4.plaquetteCoefficientProjector identity)
      T4.plaquetteCoefficientOfPlaquetteBasis

  -- An actual identified negative exponent coefficient is a distinct
  -- physical source input. The projected sign itself follows by computation.
  physicalNegativeExponentProjector :
    ∀ k u →
    CMP119.wilsonActionTerm source k
      ≡ negativeWilsonExponent u →
    T4.plaquetteCoefficientProjector
      (CMP119.wilsonActionTerm source k)
    ≡ - u
  physicalNegativeExponentProjector k u identity =
    trans
      (cong T4.plaquetteCoefficientProjector identity)
      (negativeWilsonCoefficientExact u)

------------------------------------------------------------------------
-- EXECUTABLE SOURCE-NATIVE CMP109/CMP119 REPRESENTATION: the canonical
-- existing action constructor uses +u_k on its +1 plaquette basis.
-- This is stronger than merely supplying an arbitrary coefficient field.
-- It does not determine which exponent/action convention the paper uses.
------------------------------------------------------------------------

module _
  {Density Background Fluctuation : Set}
  (trajectory : Flow.SourceNormalizedCouplingTrajectory)
  (sectors : Canonical.CMP119NormalizedSectorSource
    Density Background Fluctuation)
  where

  canonicalNodeExtractedPositiveInverse :
    ∀ k →
    T4.plaquetteCoefficientProjector
      (Canonical.canonicalNodeAction trajectory sectors k)
    ≡
    Flow.inverseCoupling trajectory k
    + (T4.plaquetteCoefficientProjector (Canonical.eAt sectors k)
    + (T4.plaquetteCoefficientProjector (Canonical.rAt sectors k)
    + (T4.plaquetteCoefficientProjector (Canonical.bAt sectors k)
    + T4.plaquetteCoefficientProjector (Canonical.vacuumAt sectors k))))
  canonicalNodeExtractedPositiveInverse k =
    positiveCanonicalNodeCoefficient
      (Flow.inverseCoupling trajectory k)
      (Canonical.eAt sectors k)
      (Canonical.rAt sectors k)
      (Canonical.bAt sectors k)
      (Canonical.vacuumAt sectors k)

