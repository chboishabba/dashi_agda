{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact where

------------------------------------------------------------------------
-- ROUND274 / TWO SOURCE INSERTIONS -> DIRECT CONNECTED CLUSTERING
--
-- NS R592 taught the proof search not to mistake an intermediate tactic for a
-- mandatory residual.  For Yang--Mills B, Heat/Doob, Langevin, Hessian anchors,
-- Dyson powers and balanced-time propagation are optional routes.  The direct
-- consumer is a geometric connected-correlation bound.
--
-- CMP116 already owns the source-side fact that finite J/source derivatives of
-- its localized analytic activities retain the positive exponential/tree
-- localization factor.  The rooted-shell compiler already proves
--
--       rootedShell(d) <= (1/4) (1/2)^d.
--
-- Therefore the only Yang--Mills-specific source seam retained here is:
--
--   the connected covariance of TWO LITERAL physical J-insertions is bounded
--   by the SAME rooted connecting-cluster shell at their support distance.
--
-- Once that is proved, this module constructs the exact R273
-- `QuantitativeCorrelationDecayTrajectory` with A = 1/4 and q = 1/2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_; _≤?_)
open import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified

------------------------------------------------------------------------
-- Power convention bridge.
------------------------------------------------------------------------

halfPowerIsRationalPower : ∀ depth →
  Geo.halfPower depth ≡ Power.rationalPower Geo.half depth
halfPowerIsRationalPower zero = refl
halfPowerIsRationalPower (suc depth)
  rewrite halfPowerIsRationalPower depth =
  ℚRing.solve-∀ (Power.rationalPower Geo.half depth) Geo.half

halfStrictlyBelowOne : Geo.half < 1ℚ
halfStrictlyBelowOne = toWitness {a? = Geo.half <? 1ℚ} _

quarterNonnegative : 0ℚ ≤ Shell.quarter
quarterNonnegative = toWitness {a? = 0ℚ ≤? Shell.quarter} _

------------------------------------------------------------------------
-- Literal two-source connected-shell source surface.
------------------------------------------------------------------------

record TwoSourceConnectedRootedShellData
    (Scale Volume Root State Observable : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    stateAtScale : Nat → State
    scaleOf : State → Scale
    volumeOf : State → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root

    -- This is already a magnitude/nonnegative connected-correlation carrier;
    -- signs/absolute values belong in the literal source adapter, not here.
    connectedCovarianceMagnitude : State → Observable → Observable → ℚ

    -- THE single live YM source seam on this direct B route.
    -- Standard log-source calculus identifies D_J^2 log Z with connected
    -- covariance.  CMP116 differentiated localization then says the surviving
    -- clusters connecting both source supports obey this rooted-shell bound.
    connectedCovarianceBelowConnectingShell : ∀ state left right →
      connectedCovarianceMagnitude state left right
      ≤ Shell.rootedShell shellData
          (scaleOf state) (volumeOf state)
          (connectingRoot state left right)
          (physicalDistance left right)

    -- No separate spatial estimate: connectedness/support geometry identifies
    -- the shell depth with the actual physical support separation.
    connectingClusterMeetsBothSupports : ∀ state left right → Set

open TwoSourceConnectedRootedShellData public

connectedCovarianceGeometricBound :
  ∀ {Scale Volume Root State Observable}
    (dataSet : TwoSourceConnectedRootedShellData
      Scale Volume Root State Observable) →
  ∀ state left right →
  connectedCovarianceMagnitude dataSet state left right
  ≤ Shell.quarter * Power.rationalPower Geo.half
      (physicalDistance dataSet left right)
connectedCovarianceGeometricBound dataSet state left right =
  let
    first = connectedCovarianceBelowConnectingShell dataSet state left right
    second = Shell.rootedShellBelowQuarterHalfPower
      (shellData dataSet)
      (scaleOf dataSet state)
      (volumeOf dataSet state)
      (connectingRoot dataSet state left right)
      (physicalDistance dataSet left right)
  in
  subst
    (λ upper → connectedCovarianceMagnitude dataSet state left right ≤ upper)
    (congQuarter
      (halfPowerIsRationalPower (physicalDistance dataSet left right)))
    (Shell.transitive (shellData dataSet) first second)
  where
  congQuarter : ∀ {left right : ℚ} → left ≡ right →
    Shell.quarter * left ≡ Shell.quarter * right
  congQuarter refl = refl

asCorrelationDecayTrajectory :
  ∀ {Scale Volume Root State Observable} →
  TwoSourceConnectedRootedShellData Scale Volume Root State Observable →
  Unified.QuantitativeCorrelationDecayTrajectory
asCorrelationDecayTrajectory dataSet = record
  { Unified.QuantitativeCorrelationDecayTrajectory.State = State
  ; Unified.QuantitativeCorrelationDecayTrajectory.Observable = Observable
  ; Unified.QuantitativeCorrelationDecayTrajectory.Correlation = State
  ; Unified.QuantitativeCorrelationDecayTrajectory.correlationProjection = λ state → state
  ; Unified.QuantitativeCorrelationDecayTrajectory.stateAtScale = stateAtScale dataSet
  ; Unified.QuantitativeCorrelationDecayTrajectory.physicalDistance =
      physicalDistance dataSet
  ; Unified.QuantitativeCorrelationDecayTrajectory.connectedCorrelationMagnitude =
      connectedCovarianceMagnitude dataSet
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitude = Shell.quarter
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratio = Geo.half
  ; Unified.QuantitativeCorrelationDecayTrajectory.amplitudeNonnegative =
      quarterNonnegative
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioNonnegative =
      Geo.halfNonnegative
  ; Unified.QuantitativeCorrelationDecayTrajectory.ratioStrictlyBelowOne =
      halfStrictlyBelowOne
  ; Unified.QuantitativeCorrelationDecayTrajectory.geometricDecayAtEveryScale =
      λ scale left right →
        connectedCovarianceGeometricBound dataSet
          (stateAtScale dataSet scale) left right
  }

round274RootedShellToConnectedCorrelationCompilerLevel : ProofLevel
round274RootedShellToConnectedCorrelationCompilerLevel = machineChecked

round274CMP116FiniteSourceDerivativeLocalizationLevel : ProofLevel
round274CMP116FiniteSourceDerivativeLocalizationLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

-- Standard generating-functional calculus, source-independent:
-- D_J log Z is the one-point function and D_J^2 log Z is connected covariance.
round274SecondLogSourceDerivativeIsConnectedCovarianceLevel : ProofLevel
round274SecondLogSourceDerivativeIsConnectedCovarianceLevel = standardImported

-- Existing finite graph fact: a connected cluster meeting both supports has a
-- path between them, whose length is at least support graph distance.
round274ConnectingClusterDiameterDominatesSupportDistanceLevel : ProofLevel
round274ConnectingClusterDiameterDominatesSupportDistanceLevel = machineChecked

-- Genuine current wall: identify the literal physical observables with two
-- source directions in CMP116's J coordinate and instantiate the corresponding
-- connected log-cluster expansion on the SAME physical RG state.
round274LiteralTwoPhysicalJInsertionsConnectedShellLevel : ProofLevel
round274LiteralTwoPhysicalJInsertionsConnectedShellLevel = conditional
