module DASHI.Analysis.RHFourWindowBiharmonicFiniteCubeExact where

-- Original owner: Lean RiemannProjectiveQuarticFourWindowAtomic,
-- PoleSameObject and SignedPoleTarget (atomic, high-pole).
-- Native reusable diagram owner: DASHI.Core.GovernedIndexedResidualCubeExact.
-- This models the INTEGER SIGNED MAGNITUDES of the *normalized* stencil,
-- not analytic cosine, Real.pi, actual zeta zeros, or a new nine-DOF theorem.
-- Source-written, NOT Agda kernel-checked; no CI.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G

-- Four original sites: 0, pi/3, pi/2, pi.  The pi/3 input is
-- preserved as TWO NONZERO source contributions with a cancellation
-- equality, rather than replaced by an empty source or a zeta zero.
-- At the selected endpoints clear denominators of 3 and 9/8:
-- 8*(3)=24=9*(8/3).  The other entries are normalized magnitudes
-- of the projective folded vector (-3,0,+4,-1).
record Source4 : Set where
  constructor source4
  field
    centreNegative : Nat
    thirdLeftScaled : Nat
    thirdRightScaled : Nat
    thirdCancellation : thirdLeftScaled ≡ thirdRightScaled
    innerPositive : Nat
    outerNegative : Nat
open Source4 public

-- Signed folded carrier: -centre +inner -outer.
data Folded3 : Set where
  folded3 : Nat → Nat → Nat → Folded3

-- Signed symmetric five-site carrier, at (-pi,-pi/2,0,pi/2,pi).
-- The constructor records (negative,positive,negative,positive,negative)
-- magnitudes.  The common scalar factor 20/351 lives in the
-- separate source normalization, not in this finite typed datum.
data SignedFive : Set where
  signedFive : Nat → Nat → Nat → Nat → Nat → SignedFive

projectFour : Source4 → Folded3
projectFour (source4 c left right witness inner outer) =
  folded3 c inner outer

unfoldFive : Folded3 → SignedFive
unfoldFive (folded3 c inner outer) =
  signedFive outer inner (c + c) inner outer

directFive : Source4 → SignedFive
directFive (source4 c left right witness inner outer) =
  signedFive outer inner (c + c) inner outer

-- A genuinely stated two-route square, not a Fourier/analytic transport.
finiteProjectiveSquare :
  (s : Source4) → directFive s ≡ unfoldFive (projectFour s)
finiteProjectiveSquare (source4 c left right witness inner outer) = refl

finiteProjectiveSquareReverse :
  (s : Source4) → unfoldFive (projectFour s) ≡ directFive s
finiteProjectiveSquareReverse (source4 c left right witness inner outer) = refl

-- The plain projected Folded3 is a LOSSY observer; a true BIDI path
-- must carry the original Source4 through the observation. Both layers
-- remain separate, and downstream consumers can recover source coordinates.
record TracedFold : Set where
  constructor tracedFold
  field
    originalFour : Source4
    foldedObservation : Folded3
open TracedFold public

record TracedFive : Set where
  constructor tracedFive
  field
    originalFiveSource : Source4
    fiveObservation : SignedFive
open TracedFive public

projectWithSource : Source4 → TracedFold
projectWithSource s = tracedFold s (projectFour s)

unfoldWithSource : TracedFold → TracedFive
unfoldWithSource (tracedFold s f) = tracedFive s (unfoldFive f)

directWithSource : Source4 → TracedFive
directWithSource s = tracedFive s (directFive s)

tracedProjectiveSquare :
  (s : Source4) →
  directWithSource s ≡ unfoldWithSource (projectWithSource s)
tracedProjectiveSquare (source4 c left right witness inner outer) = refl

tracedProjectiveSquareReverse :
  (s : Source4) →
  unfoldWithSource (projectWithSource s) ≡ directWithSource s
tracedProjectiveSquareReverse (source4 c left right witness inner outer) = refl

sourceRecoveredFromProjection :
  (s : Source4) → originalFour (projectWithSource s) ≡ s
sourceRecoveredFromProjection s = refl

sourceRecoveredFromFive :
  (s : Source4) → originalFiveSource (directWithSource s) ≡ s
sourceRecoveredFromFive s = refl

reflectFive : SignedFive → SignedFive
reflectFive (signedFive a b c d e) = signedFive e d c b a

unfoldReflectionInvariant : (f : Folded3) →
  reflectFive (unfoldFive f) ≡ unfoldFive f
unfoldReflectionInvariant (folded3 c inner outer) = refl

-- Reuse the ORIGINAL H05 eight-vertex/twelve-map/six-face carrier.
-- x=projective elimination, y=direct symmetry expansion,
-- z=IDENTITY history comparison.  The third axis is deliberately
-- degenerate: it does NOT certify Bishop analytic/finite-pole transport.
finiteH05Cube : Q.Cube
finiteH05Cube = record
  { A = Source4 ; B = TracedFold ; C = TracedFive ; D = TracedFive
  ; E = Source4 ; F = TracedFold ; H = TracedFive ; I = TracedFive
  ; x00 = projectWithSource ; x10 = λ x → x
  ; x01 = projectWithSource ; x11 = λ x → x
  ; y00 = directWithSource ; y10 = unfoldWithSource
  ; y01 = directWithSource ; y11 = unfoldWithSource
  ; z00 = λ x → x ; z10 = λ x → x
  ; z01 = λ x → x ; z11 = λ x → x
  }

finiteH05Residuals : Q.Faces finiteH05Cube
finiteH05Residuals = record
  { Rxy0 = λ _ → ⊤ ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
  ; Rxy1 = λ _ → ⊤ ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
  }

-- Every one of six finite H05 faces is explicit.  Four of the
-- six faces are identity naturality, while two are the actual
-- project/unfold square; neither a full analytic cube nor nine-DOF
-- chart source can be inferred from this fixture.
finiteH05ExactFaces : Q.ExactFaces finiteH05Cube finiteH05Residuals
finiteH05ExactFaces = record
  { pxy0 = G.commutingSquareWitness tracedProjectiveSquareReverse
  ; pxz0 = G.commutingSquareWitness (λ _ → refl)
  ; pyz0 = G.commutingSquareWitness (λ _ → refl)
  ; pxy1 = G.commutingSquareWitness tracedProjectiveSquareReverse
  ; pxz1 = G.commutingSquareWitness (λ _ → refl)
  ; pyz1 = G.commutingSquareWitness (λ _ → refl)
  }

-- A generic ledger index can be the ORIGINAL nine-DOF/hyperfibre
-- coordinate type, rather than reducing it to a number.  Sign,
-- residual, tagged mode, and observed-zero data stay separate.
record IndexedSource
  (Index Sign Residual Mode Observation Payload : Set) : Set where
  constructor indexedSource
  field
    index : Index
    sign : Sign
    residual : Residual
    mode : Mode
    observation : Observation
    payload : Payload
open IndexedSource public

mapIndexedPayload :
  ∀ {Index Sign Residual Mode Observation X Y : Set} →
  (X → Y) →
  IndexedSource Index Sign Residual Mode Observation X →
  IndexedSource Index Sign Residual Mode Observation Y
mapIndexedPayload f (indexedSource k s r m o x) =
  indexedSource k s r m o (f x)

projectIndexed :
  ∀ {Index Sign Residual Mode Observation : Set} →
  IndexedSource Index Sign Residual Mode Observation Source4 →
  IndexedSource Index Sign Residual Mode Observation TracedFold
projectIndexed = mapIndexedPayload projectWithSource

unfoldIndexed :
  ∀ {Index Sign Residual Mode Observation : Set} →
  IndexedSource Index Sign Residual Mode Observation TracedFold →
  IndexedSource Index Sign Residual Mode Observation TracedFive
unfoldIndexed = mapIndexedPayload unfoldWithSource

directIndexed :
  ∀ {Index Sign Residual Mode Observation : Set} →
  IndexedSource Index Sign Residual Mode Observation Source4 →
  IndexedSource Index Sign Residual Mode Observation TracedFive
directIndexed = mapIndexedPayload directWithSource

indexedProjectiveSquare :
  ∀ {Index Sign Residual Mode Observation : Set}
  (f : IndexedSource Index Sign Residual Mode Observation Source4) →
  directIndexed f ≡ unfoldIndexed (projectIndexed f)
indexedProjectiveSquare
  (indexedSource k s r m o (source4 c left right witness inner outer)) = refl

-- Original pi/3 input history is inhabited and nonempty, despite
-- its observed cancellation in the projected profile.
sampleFour : Source4
sampleFour = source4 3 24 24 refl 4 1

sampleHistoryNotErased : thirdLeftScaled sampleFour ≡ 24
sampleHistoryNotErased = refl

sampleOtherFour : Source4
sampleOtherFour = source4 3 48 48 refl 4 1

sampleLossyCollision : projectFour sampleFour ≡ projectFour sampleOtherFour
sampleLossyCollision = refl

sampleOtherHistoryNotErased : thirdLeftScaled sampleOtherFour ≡ 48
sampleOtherHistoryNotErased = refl

sampleTrackedSourceRecovered :
  originalFiveSource (directWithSource sampleFour) ≡ sampleFour
sampleTrackedSourceRecovered = refl

sampleFive : directFive sampleFour ≡ signedFive 1 4 6 4 1
sampleFive = refl

sampleIndexedSquare : ∀ {Index Sign Residual Mode Observation : Set}
  (k : Index) (s : Sign) (r : Residual) (m : Mode) (o : Observation) →
  directIndexed (indexedSource k s r m o sampleFour)
    ≡ unfoldIndexed (projectIndexed (indexedSource k s r m o sampleFour))
sampleIndexedSquare k s r m o = refl

-- NOT paid: independent geometry charts on nine-DOF, source-refinement,
-- finite-t/smooth analyticity, Bishop pi = Lean Real.pi, indexed
-- Frobenius/source history, and any map into actual ζ zero measures.
