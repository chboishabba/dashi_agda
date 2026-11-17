module DASHI.Physics.Photovoltaic.Atomic369BasisTransportNoFreeGainExact where

-- Exact generic no-free-gain theorem for a mere change of coordinates.
-- Reuses the source atomic p-shell/trigonal carriers; DO NOT confuse this
-- finite label equivalence with an analytic Hilbert SALC unitary, actual
-- Wannier same-material sewing, or observed photovoltaic performance.
-- The existing CoTaSe2 Wannier BNS owner imposes the same-basis covariance
-- discipline; its material sewing matrix is NOT reused as a GaAs matrix.
-- Agda Golden typecheck still OPEN.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as P
import DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact as T
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierBNSCovarianceExact as Prior

cong : {A B : Set} {x y : A} (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

record ExactCoordinateEquivalence : Set₁ where
  field
    A B : Set
    encode : A -> B
    decode : B -> A
    decodeEncode : (a : A) -> decode (encode a) ≡ a
    encodeDecode : (b : B) -> encode (decode b) ≡ b

open ExactCoordinateEquivalence public

-- Rather than assuming a new readout theorem, the observed B-readout is
-- defined as transport of the SAME original observable along the isomorphism.
transportReadout :
  (e : ExactCoordinateEquivalence) ->
  (A e -> Nat) -> B e -> Nat
transportReadout e readout b = readout (decode e b)

transportReadoutConservesEveryValue :
  (e : ExactCoordinateEquivalence) ->
  (readout : A e -> Nat) ->
  (a : A e) ->
  transportReadout e readout (encode e a) ≡ readout a
transportReadoutConservesEveryValue e readout a =
  cong readout (decodeEncode e a)

transportOperator :
  (e : ExactCoordinateEquivalence) ->
  (A e -> A e) ->
  B e -> B e
transportOperator e H b = encode e (H (decode e b))

transportOperatorIntertwines :
  (e : ExactCoordinateEquivalence) ->
  (H : A e -> A e) ->
  (a : A e) ->
  transportOperator e H (encode e a) ≡ encode e (H a)
transportOperatorIntertwines e H a =
  cong (λ x -> encode e (H x)) (decodeEncode e a)

-- Finite p/magnetic -> trigonal-character label transport, sourced from
-- the original 369 owner; actual complex linear SALCs remain separate.
trigonalToMagnetic : T.Trigonal -> P.MagneticState
trigonalToMagnetic T.eMinus = P.mNegOne
trigonalToMagnetic T.a1 = P.mZero
trigonalToMagnetic T.ePlus = P.mPosOne

magneticRoundTrip : (m : P.MagneticState) ->
  trigonalToMagnetic (T.sourcePToTrigonal m) ≡ m
magneticRoundTrip P.mNegOne = refl
magneticRoundTrip P.mZero = refl
magneticRoundTrip P.mPosOne = refl

trigonalRoundTrip : (m : T.Trigonal) ->
  T.sourcePToTrigonal (trigonalToMagnetic m) ≡ m
trigonalRoundTrip T.a1 = refl
trigonalRoundTrip T.ePlus = refl
trigonalRoundTrip T.eMinus = refl

canonicalAtomicTrigonalLabelEquivalence : ExactCoordinateEquivalence
canonicalAtomicTrigonalLabelEquivalence =
  record
    { A = P.MagneticState
    ; B = T.Trigonal
    ; encode = T.sourcePToTrigonal
    ; decode = trigonalToMagnetic
    ; decodeEncode = magneticRoundTrip
    ; encodeDecode = trigonalRoundTrip
    }

-- The same projection works for ANY Nat-valued source observable, not
-- only an arbitrarily chosen oscillator or charge count.
sourceLabelReadoutUnchanged :
  (readout : P.MagneticState -> Nat) (m : P.MagneticState) ->
  transportReadout canonicalAtomicTrigonalLabelEquivalence
    readout (T.sourcePToTrigonal m) ≡ readout m
sourceLabelReadoutUnchanged =
  transportReadoutConservesEveryValue canonicalAtomicTrigonalLabelEquivalence

-- No physical 369 advantage follows from the above mere relabeling.
-- A new material state/strain/defect field, transport law or light-source
-- coupling is an additional physical operator, NOT a coordinate transform.
