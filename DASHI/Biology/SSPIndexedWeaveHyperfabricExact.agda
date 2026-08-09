module DASHI.Biology.SSPIndexedWeaveHyperfabricExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPHyperfibreSymmetryTowerExact as Tower

------------------------------------------------------------------------
-- Lawful upgrade of the existing SSP hyperfibre atlas.
--
-- Paths retain the repository's three FibreOrientation values rather than
-- replacing them by a fresh Boolean.  Composition adjoins a global mediated
-- identity to the two-element {forward,inverse} subgroup:
--
--   mediated is the path identity;
--   forward is the identity inside the nontrivial transport component;
--   inverse * inverse = forward.
--
-- The existing lane action is a monoid action: mediated and forward preserve
-- lane state, inverse reverses polarity.  All laws are proved by finite cases.
------------------------------------------------------------------------

composeOrientation :
  SSP.FibreOrientation →
  SSP.FibreOrientation →
  SSP.FibreOrientation
composeOrientation SSP.mediatedOrientation orientation = orientation
composeOrientation SSP.forwardOrientation SSP.mediatedOrientation =
  SSP.forwardOrientation
composeOrientation SSP.inverseOrientation SSP.mediatedOrientation =
  SSP.inverseOrientation
composeOrientation SSP.forwardOrientation SSP.forwardOrientation =
  SSP.forwardOrientation
composeOrientation SSP.forwardOrientation SSP.inverseOrientation =
  SSP.inverseOrientation
composeOrientation SSP.inverseOrientation SSP.forwardOrientation =
  SSP.inverseOrientation
composeOrientation SSP.inverseOrientation SSP.inverseOrientation =
  SSP.forwardOrientation

composeOrientationIdLeft :
  (orientation : SSP.FibreOrientation) →
  composeOrientation SSP.mediatedOrientation orientation ≡ orientation
composeOrientationIdLeft SSP.inverseOrientation = refl
composeOrientationIdLeft SSP.mediatedOrientation = refl
composeOrientationIdLeft SSP.forwardOrientation = refl

composeOrientationIdRight :
  (orientation : SSP.FibreOrientation) →
  composeOrientation orientation SSP.mediatedOrientation ≡ orientation
composeOrientationIdRight SSP.inverseOrientation = refl
composeOrientationIdRight SSP.mediatedOrientation = refl
composeOrientationIdRight SSP.forwardOrientation = refl

composeOrientationAssoc :
  (r q p : SSP.FibreOrientation) →
  composeOrientation (composeOrientation r q) p
  ≡ composeOrientation r (composeOrientation q p)
composeOrientationAssoc SSP.mediatedOrientation SSP.mediatedOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.mediatedOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.mediatedOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.forwardOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.forwardOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.forwardOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.inverseOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.inverseOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.mediatedOrientation SSP.inverseOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.mediatedOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.mediatedOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.mediatedOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.forwardOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.forwardOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.forwardOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.inverseOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.inverseOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.forwardOrientation SSP.inverseOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.mediatedOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.mediatedOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.mediatedOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.forwardOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.forwardOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.forwardOrientation SSP.inverseOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.inverseOrientation SSP.mediatedOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.inverseOrientation SSP.forwardOrientation = refl
composeOrientationAssoc SSP.inverseOrientation SSP.inverseOrientation SSP.inverseOrientation = refl

SSPWeaveState : SSP.SSPPrime → Set
SSPWeaveState lane = Tower.LaneState

data SSPWeavePath : SSP.SSPPrime → SSP.SSPPrime → Set where
  lanePath :
    {source target : SSP.SSPPrime} →
    SSP.FibreOrientation →
    SSPWeavePath source target

pathOrientation :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  SSP.FibreOrientation
pathOrientation (lanePath orientation) = orientation

identitySSPPath :
  (lane : SSP.SSPPrime) →
  SSPWeavePath lane lane
identitySSPPath lane = lanePath SSP.mediatedOrientation

infixr 40 _thenSSP_

_thenSSP_ :
  {source middle target : SSP.SSPPrime} →
  SSPWeavePath middle target →
  SSPWeavePath source middle →
  SSPWeavePath source target
_thenSSP_ (lanePath q) (lanePath p) =
  lanePath (composeOrientation q p)

sspPathIdLeft :
  {source target : SSP.SSPPrime} →
  (path : SSPWeavePath source target) →
  identitySSPPath target thenSSP path ≡ path
sspPathIdLeft (lanePath orientation)
  rewrite composeOrientationIdLeft orientation = refl

sspPathIdRight :
  {source target : SSP.SSPPrime} →
  (path : SSPWeavePath source target) →
  path thenSSP identitySSPPath source ≡ path
sspPathIdRight (lanePath orientation)
  rewrite composeOrientationIdRight orientation = refl

sspPathAssoc :
  {i j k l : SSP.SSPPrime} →
  (r : SSPWeavePath k l) →
  (q : SSPWeavePath j k) →
  (p : SSPWeavePath i j) →
  (r thenSSP q) thenSSP p ≡ r thenSSP (q thenSSP p)
sspPathAssoc (lanePath r) (lanePath q) (lanePath p)
  rewrite composeOrientationAssoc r q p = refl

transportOrientation :
  SSP.FibreOrientation →
  Tower.LaneState →
  Tower.LaneState
transportOrientation orientation state =
  Tower.laneOrientationAction orientation state

transportOrientationComposition :
  (q p : SSP.FibreOrientation) →
  (state : Tower.LaneState) →
  transportOrientation (composeOrientation q p) state
  ≡ transportOrientation q (transportOrientation p state)
transportOrientationComposition SSP.mediatedOrientation SSP.mediatedOrientation state = refl
transportOrientationComposition SSP.mediatedOrientation SSP.forwardOrientation state = refl
transportOrientationComposition SSP.mediatedOrientation SSP.inverseOrientation state = refl
transportOrientationComposition SSP.forwardOrientation SSP.mediatedOrientation state = refl
transportOrientationComposition SSP.forwardOrientation SSP.forwardOrientation state = refl
transportOrientationComposition SSP.forwardOrientation SSP.inverseOrientation state = refl
transportOrientationComposition SSP.inverseOrientation SSP.mediatedOrientation state = refl
transportOrientationComposition SSP.inverseOrientation SSP.forwardOrientation state = refl
transportOrientationComposition SSP.inverseOrientation SSP.inverseOrientation Tower.negativeLaneState = refl
transportOrientationComposition SSP.inverseOrientation SSP.inverseOrientation Tower.mediatedLaneState = refl
transportOrientationComposition SSP.inverseOrientation SSP.inverseOrientation Tower.positiveLaneState = refl

transportSSP :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  SSPWeaveState source →
  SSPWeaveState target
transportSSP (lanePath orientation) state =
  transportOrientation orientation state

transportSSPIdentity :
  (lane : SSP.SSPPrime) →
  (state : SSPWeaveState lane) →
  transportSSP (identitySSPPath lane) state ≡ state
transportSSPIdentity lane state = refl

transportSSPComposition :
  {source middle target : SSP.SSPPrime} →
  (q : SSPWeavePath middle target) →
  (p : SSPWeavePath source middle) →
  (state : SSPWeaveState source) →
  transportSSP (q thenSSP p) state
  ≡ transportSSP q (transportSSP p state)
transportSSPComposition (lanePath q) (lanePath p) state =
  transportOrientationComposition q p state

SSPResidual : SSP.SSPPrime → Set
SSPResidual lane = SSP.FibreOrientation

sspStateResidual :
  (lane : SSP.SSPPrime) →
  SSPWeaveState lane →
  SSPResidual lane
sspStateResidual lane state = SSP.mediatedOrientation

sspResidualAfter :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  SSPWeaveState source →
  SSPResidual target
sspResidualAfter path state = pathOrientation path

sspResidualIdentity :
  (lane : SSP.SSPPrime) →
  (state : SSPWeaveState lane) →
  sspResidualAfter (identitySSPPath lane) state
  ≡ sspStateResidual lane state
sspResidualIdentity lane state = refl

canonicalSSPIndexedWeave :
  Indexed.IndexedWeave SSP.SSPPrime SSPWeaveState
canonicalSSPIndexedWeave =
  record
    { Path = SSPWeavePath
    ; idPath = identitySSPPath
    ; _∙_ = _thenSSP_
    ; pathIdLeft = sspPathIdLeft
    ; pathIdRight = sspPathIdRight
    ; pathAssoc = sspPathAssoc
    ; transport = transportSSP
    ; transportId = transportSSPIdentity
    ; transportComp = transportSSPComposition
    ; Residual = SSPResidual
    ; stateResidual = sspStateResidual
    ; residualAfter = sspResidualAfter
    ; residualId = sspResidualIdentity
    }

inverseTwicePreservesEveryLaneState :
  (source middle target : SSP.SSPPrime) →
  (state : SSPWeaveState source) →
  transportSSP
    (_thenSSP_
      (lanePath {source = middle} {target = target} SSP.inverseOrientation)
      (lanePath {source = source} {target = middle} SSP.inverseOrientation))
    state
  ≡ state
inverseTwicePreservesEveryLaneState source middle target state =
  transportOrientationComposition
    SSP.inverseOrientation
    SSP.inverseOrientation
    state

inverseTwiceComposesToForward :
  composeOrientation SSP.inverseOrientation SSP.inverseOrientation
  ≡ SSP.forwardOrientation
inverseTwiceComposesToForward = refl

inversePathRetainsTargetResidual :
  {source target : SSP.SSPPrime} →
  (state : SSPWeaveState source) →
  sspResidualAfter
    (lanePath {source = source} {target = target} SSP.inverseOrientation)
    state
  ≡ SSP.inverseOrientation
inversePathRetainsTargetResidual state = refl

forwardPathRetainsTargetResidual :
  {source target : SSP.SSPPrime} →
  (state : SSPWeaveState source) →
  sspResidualAfter
    (lanePath {source = source} {target = target} SSP.forwardOrientation)
    state
  ≡ SSP.forwardOrientation
forwardPathRetainsTargetResidual state = refl
