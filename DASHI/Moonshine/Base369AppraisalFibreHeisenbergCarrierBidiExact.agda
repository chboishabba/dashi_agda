module DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact where

------------------------------------------------------------------------
-- BASE369 APPRAISAL FIBRE <-> MONSTER 3B FINITE HEISENBERG CARRIER
--
-- Exact carrier fact:
--   appraisal fibre = T3 x T3 = 3^6 = 729 states
--   finite Heisenberg X6 = F3^6         = 729 states
--
-- This module constructs the coordinate-wise bijection.  It does NOT claim
-- that the geometric fibre is automatically the Monster 3B representation;
-- operator equivariance is a separate obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg

------------------------------------------------------------------------
-- 1. Exact trit chart.
------------------------------------------------------------------------

sspToTrit : SSP.SSPTrit → Trit
sspToTrit SSP.sspNegOne = neg
sspToTrit SSP.sspZero = zer
sspToTrit SSP.sspPosOne = pos

tritToSSP : Trit → SSP.SSPTrit
tritToSSP neg = SSP.sspNegOne
tritToSSP zer = SSP.sspZero
tritToSSP pos = SSP.sspPosOne

sspTritRoundTrip : (t : SSP.SSPTrit) → tritToSSP (sspToTrit t) ≡ t
sspTritRoundTrip SSP.sspNegOne = refl
sspTritRoundTrip SSP.sspZero = refl
sspTritRoundTrip SSP.sspPosOne = refl

tritSSPRoundTrip : (t : Trit) → sspToTrit (tritToSSP t) ≡ t
tritSSPRoundTrip neg = refl
tritSSPRoundTrip zer = refl
tritSSPRoundTrip pos = refl

------------------------------------------------------------------------
-- 2. Exact appraisal-fibre <-> X6 chart.
------------------------------------------------------------------------

appraisalFibreToX6 : Geometry.AppraisalFibrePoint → Heisenberg.X6
appraisalFibreToX6
  (Geometry.appraisalFibrePoint
    (Geometry.ternary27Point a0 a1 a2)
    (Geometry.ternary27Point b0 b1 b2)) =
  Heisenberg.x6
    (sspToTrit a0) (sspToTrit a1) (sspToTrit a2)
    (sspToTrit b0) (sspToTrit b1) (sspToTrit b2)

x6ToAppraisalFibre : Heisenberg.X6 → Geometry.AppraisalFibrePoint
x6ToAppraisalFibre (Heisenberg.x6 a0 a1 a2 b0 b1 b2) =
  Geometry.appraisalFibrePoint
    (Geometry.ternary27Point
      (tritToSSP a0) (tritToSSP a1) (tritToSSP a2))
    (Geometry.ternary27Point
      (tritToSSP b0) (tritToSSP b1) (tritToSSP b2))

appraisalFibreRoundTrip :
  (f : Geometry.AppraisalFibrePoint) →
  x6ToAppraisalFibre (appraisalFibreToX6 f) ≡ f
appraisalFibreRoundTrip
  (Geometry.appraisalFibrePoint
    (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne)
    (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne)) = refl
appraisalFibreRoundTrip
  (Geometry.appraisalFibrePoint
    (Geometry.ternary27Point a0 a1 a2)
    (Geometry.ternary27Point b0 b1 b2))
  rewrite sspTritRoundTrip a0 | sspTritRoundTrip a1 | sspTritRoundTrip a2
        | sspTritRoundTrip b0 | sspTritRoundTrip b1 | sspTritRoundTrip b2 = refl

x6RoundTrip :
  (x : Heisenberg.X6) →
  appraisalFibreToX6 (x6ToAppraisalFibre x) ≡ x
x6RoundTrip (Heisenberg.x6 a0 a1 a2 b0 b1 b2)
  rewrite tritSSPRoundTrip a0 | tritSSPRoundTrip a1 | tritSSPRoundTrip a2
        | tritSSPRoundTrip b0 | tritSSPRoundTrip b1 | tritSSPRoundTrip b2 = refl

------------------------------------------------------------------------
-- 3. Full hyperfabric factorisation into interaction base x Heisenberg fibre.
------------------------------------------------------------------------

record InteractionHeisenbergPoint : Set where
  constructor interactionHeisenbergPoint
  field
    interactionBase : Geometry.Ternary27Point
    heisenbergFibre : Heisenberg.X6
open InteractionHeisenbergPoint public

fabricToInteractionHeisenberg :
  Geometry.TernaryHyperformalPoint → InteractionHeisenbergPoint
fabricToInteractionHeisenberg p =
  interactionHeisenbergPoint
    (Geometry.projectInteractionVoxel p)
    (appraisalFibreToX6 (Geometry.projectAppraisalFibre p))

interactionHeisenbergToFabric :
  InteractionHeisenbergPoint → Geometry.TernaryHyperformalPoint
interactionHeisenbergToFabric (interactionHeisenbergPoint base fibre) =
  Geometry.rebuildOverInteraction base (x6ToAppraisalFibre fibre)

fabricHeisenbergRoundTrip :
  (p : Geometry.TernaryHyperformalPoint) →
  interactionHeisenbergToFabric (fabricToInteractionHeisenberg p) ≡ p
fabricHeisenbergRoundTrip
  (Geometry.ternaryHyperformalPoint base a b)
  rewrite appraisalFibreRoundTrip (Geometry.appraisalFibrePoint a b) = refl

heisenbergFabricRoundTrip :
  (p : InteractionHeisenbergPoint) →
  fabricToInteractionHeisenberg (interactionHeisenbergToFabric p) ≡ p
heisenbergFabricRoundTrip (interactionHeisenbergPoint base fibre)
  rewrite x6RoundTrip fibre = refl

------------------------------------------------------------------------
-- 4. Exact cardinal factorisation used by both geometric and Heisenberg lanes.
------------------------------------------------------------------------

interactionStateCount : Nat
interactionStateCount = 27

heisenbergFibreStateCount : Nat
heisenbergFibreStateCount = Heisenberg.schrodingerBasisDimension

factorisedFabricStateCount : Nat
factorisedFabricStateCount = interactionStateCount * heisenbergFibreStateCount

heisenbergFibreStateCountIs729 : heisenbergFibreStateCount ≡ 729
heisenbergFibreStateCountIs729 = refl

factorisedFabricStateCountIs19683 : factorisedFabricStateCount ≡ 19683
factorisedFabricStateCountIs19683 = refl

factorisedCountAgreesWithGeometry :
  factorisedFabricStateCount ≡ Geometry.hyperfabricStateCount
factorisedCountAgreesWithGeometry = refl

------------------------------------------------------------------------
-- 5. BIDI boundary: exact carrier equivalence != representation equivalence.
------------------------------------------------------------------------

record AppraisalHeisenbergCarrierBoundary : Set where
  constructor appraisalHeisenbergCarrierBoundary
  field
    sixTritCarrierBijectionConstructed : Bool
    fibreCardinalityMatchesSchrodingerBasis : Bool
    fullFabricFactorsAsTwentySevenTimesSevenTwentyNine : Bool
    heisenbergTranslationsIntertwinedWithGeometricTransport : Bool
    heisenbergModulationsIntertwinedWithGeometricObservables : Bool
    monster3BRepresentationEstablished : Bool

canonicalAppraisalHeisenbergCarrierBoundary : AppraisalHeisenbergCarrierBoundary
canonicalAppraisalHeisenbergCarrierBoundary =
  appraisalHeisenbergCarrierBoundary true true true false false false
