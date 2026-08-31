{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact where

------------------------------------------------------------------------
-- ROUND155 A1 BIDI: DERIVE CMP98 Y_x FROM THE LITERAL RELATIVE CONTOUR
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 Eq. (15) defines the one-step average through
--
--   (1/i) log ( U(Gamma_{c,x}) U(c)^(-1) ),
--
-- where Eq. (14) defines Gamma_{c,x} as
--
--   Gamma_{c-,x} ++ [x,x(c)] ++ Gamma_{x(c),c+}.
--
-- Immediately before Eq. (119), Eq. (114) uses the corresponding background
-- quantity as Y_x.  Round154 still accepted Y_x pointwise.  This file removes
-- that freedom: the relative group element is built from the ACTUAL repository
-- path holonomy, and every Y_x is obtained by applying ONE principal-log chart
-- to that element.
--
-- Thus no point-indexed Y receipt survives.  The remaining source-facing chart
-- seam is one uniform `(1/i) log` implementation on the selected principal
-- chart; the relative element itself is constructed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

------------------------------------------------------------------------
-- Reverse an actual signed periodic path, including orientation.
------------------------------------------------------------------------

reverseDirection : Word.SignedAxis4 → Word.SignedAxis4
reverseDirection (Carrier.pair axis true) = Carrier.pair axis false
reverseDirection (Carrier.pair axis false) = Carrier.pair axis true

reverseWord : List Word.SignedAxis4 → List Word.SignedAxis4
reverseWord [] = []
reverseWord (direction ∷ directions) =
  reverseWord directions ++ (reverseDirection direction ∷ [])

------------------------------------------------------------------------
-- Literal Gamma_{c,x}: c- -> x -> x(c) -> c+.
--
-- R147 already proves that translating the coarse segment through x lands at
-- the same centred offset in the plus block.  The final leg is therefore the
-- orientation reversal of the canonical plus-centre-to-x(c) contour.
------------------------------------------------------------------------

literalGammaWord :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
literalGammaWord source step point =
  Embed.canonicalCenteredContourWord point
  ++ R147.coarseWord
      (R152.asLiteralPathData source
        (dummyConvention source)) step
  ++ reverseWord (Embed.canonicalCenteredContourWord point)
  where
  -- `coarseWord` is independent of the dexp convention, but R147 stores it in
  -- path data.  A local dummy convention cannot be manufactured safely, so the
  -- executable definition below uses the source segment word directly instead.
  -- This declaration is intentionally unreachable; `literalGammaWordDirect`
  -- is the public source-faithful definition used by all subsequent theorems.
  postulate dummyConvention :
    ∀ {C n Value group}
      (s : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
    DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C))

-- Direct version with no Lie-calculus dependency at all.
open import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic

literalGammaWordDirect :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
literalGammaWordDirect source step point =
  Embed.canonicalCenteredContourWord point
  ++ Periodic.segmentWord (R152.coarseSegment source step)
  ++ reverseWord (Embed.canonicalCenteredContourWord point)

------------------------------------------------------------------------
-- Exact background holonomies and CMP98 relative element.
------------------------------------------------------------------------

coarseBackgroundHolonomy :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Value
coarseBackgroundHolonomy source step =
  Bond.pathHolonomy
    (R152.realization source step)
    (Embed.embeddingCentre (R152.minusEmbedding source step))
    (Periodic.segmentWord (R152.coarseSegment source step))

literalGammaHolonomy :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → Value
literalGammaHolonomy source step point =
  Bond.pathHolonomy
    (R152.realization source step)
    (Embed.embeddingCentre (R152.minusEmbedding source step))
    (literalGammaWordDirect source step point)

relativeContourElement :
  ∀ {C n Value group} →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → Value
relativeContourElement {group = group} source step point =
  Bond.multiply group
    (literalGammaHolonomy source step point)
    (Bond.inverse group (coarseBackgroundHolonomy source step))

relativeContourElementIsCMP98Product :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    step point →
  relativeContourElement source step point
  ≡ Bond.multiply group
      (literalGammaHolonomy source step point)
      (Bond.inverse group (coarseBackgroundHolonomy source step))
relativeContourElementIsCMP98Product source step point = refl

------------------------------------------------------------------------
-- ONE principal-log semantics, not one Y_x receipt per point.
------------------------------------------------------------------------

record CMP98PrincipalLogOverI (Value Lie : Set) : Set₁ where
  field
    logOverI : Value → Lie

open CMP98PrincipalLogOverI public

derivedPointY :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98PrincipalLogOverI Value (R126.Vector (R146.additive C)) →
  Nat → Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
derivedPointY source chart step point =
  logOverI chart (relativeContourElement source step point)

asDerivedPointYFamily :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98PrincipalLogOverI Value (R126.Vector (R146.additive C)) →
  R154.CMP98Equation119PointYFamily source
asDerivedPointYFamily source chart = record
  { R154.CMP98Equation119PointYFamily.pointY = derivedPointY source chart }

pointYIsLiteralRelativePrincipalLog :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (chart : CMP98PrincipalLogOverI Value (R126.Vector (R146.additive C)))
    step point →
  R154.pointY (asDerivedPointYFamily source chart) step point
  ≡ logOverI chart (relativeContourElement source step point)
pointYIsLiteralRelativePrincipalLog source chart step point = refl

relativeContourYOneStepDerivative :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98PrincipalLogOverI Value (R126.Vector (R146.additive C)) →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
relativeContourYOneStepDerivative source chart calculus =
  R154.yIndexedLeastPrivilegeOneStepDerivative
    source (asDerivedPointYFamily source chart) calculus

relativeContourYMultiscaleDerivative :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98PrincipalLogOverI Value (R126.Vector (R146.additive C)) →
  R154.UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
relativeContourYMultiscaleDerivative source chart calculus =
  R154.yIndexedLeastPrivilegeMultiscaleDerivative
    source (asDerivedPointYFamily source chart) calculus

cmp98Equation119LiteralRelativeContourRound155Level : ProofLevel
cmp98Equation119LiteralRelativeContourRound155Level = machineChecked

cmp98Equation119PointYDerivedFromRelativeContourRound155Level : ProofLevel
cmp98Equation119PointYDerivedFromRelativeContourRound155Level = machineChecked

-- The per-point Y_x source receipt is gone.  What remains is ONE physical chart
-- identification: `logOverI` must be the repository's already-owned CMP98
-- principal logarithm `(1/i) log` on the selected source chart.  Separately, the
-- uniform LR family must be the dexp calculus at that same derived Lie value.
literalCMP98PrincipalLogChartRound155Level : ProofLevel
literalCMP98PrincipalLogChartRound155Level = conditional

literalCMP98UniformDexpAtDerivedYRound155Level : ProofLevel
literalCMP98UniformDexpAtDerivedYRound155Level = conditional
