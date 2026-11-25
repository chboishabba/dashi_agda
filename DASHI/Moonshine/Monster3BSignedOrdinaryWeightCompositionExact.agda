module DASHI.Moonshine.Monster3BSignedOrdinaryWeightCompositionExact where

-- Same literal phase restrictions, actual linear frame and ordinary chart.
-- Inspired by the indexed arrow/order discipline of PR #1552, not a claim
-- that the ultrametric cube itself is the Monster representation.
-- Character recognition supplies the ordinary vacuum isomorphism; its
-- actual inhabitants, linear field laws and kernel acceptance are separate.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)
import DASHI.Geometry.HilbertLorentzForcing as L
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as I
import DASHI.Moonshine.Monster3BActualLinearWeightFrameExact as F
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as Z

record VacuumChart (A : F.ActualLinearWeightFrame) : Set₁ where
  field
    ordinary : L.HilbertLift
    scalarToOrdinary : L.Scalar (F.vacuum A) → L.Scalar ordinary
    encode : L.Vector (F.vacuum A) → L.Vector ordinary
    decode : L.Vector ordinary → L.Vector (F.vacuum A)
    decodeEncode : ∀ u → decode (encode u) ≡ u
    encodeDecode : ∀ u → encode (decode u) ≡ u
    encodeAdd : ∀ u v → encode (L._+_ (F.vacuum A) u v) ≡
      L._+_ ordinary (encode u) (encode v)
    encodeScale : ∀ a u → encode (L._·_ (F.vacuum A) a u) ≡
      L._·_ ordinary (scalarToOrdinary a) (encode u)

open VacuumChart public

Coordinates : ∀ {A} → VacuumChart A → Set
Coordinates C = H.X6 → L.Vector (ordinary C)

toOrdinary : ∀ {A} (C : VacuumChart A) → L.Vector (F.sector A) → Coordinates C
toOrdinary {A} C w x = encode C (F.recoverWeight A x w)

fromOrdinary : ∀ {A} (C : VacuumChart A) → Coordinates C → L.Vector (F.sector A)
fromOrdinary {A} C u = F.evaluate A (λ x → decode C (u x))

toAfterFrom : ∀ {A} (C : VacuumChart A) (u : Coordinates C) (x : H.X6) →
  toOrdinary C (fromOrdinary C u) x ≡ u x
toAfterFrom {A} C u x =
  trans (cong (encode C) (F.recoverAfterEvaluate A (λ y → decode C (u y)) x))
        (encodeDecode C (u x))

fromAfterTo : ∀ {A} (C : VacuumChart A) (w : L.Vector (F.sector A)) →
  fromOrdinary C (toOrdinary C w) ≡ w
fromAfterTo {A} C w =
  trans (F.sumSectorCong A _ _
    (λ x → cong (F.includeWeight A x) (decodeEncode C (F.recoverWeight A x w))))
    (F.evaluateAfterRecover A w)

toOrdinaryAdd : ∀ {A} (C : VacuumChart A) (u v : L.Vector (F.sector A)) (x : H.X6) →
  toOrdinary C (L._+_ (F.sector A) u v) x ≡
  L._+_ (ordinary C) (toOrdinary C u x) (toOrdinary C v x)
toOrdinaryAdd {A} C u v x =
  trans (cong (encode C) (F.recoverAdd A x u v))
        (encodeAdd C (F.recoverWeight A x u) (F.recoverWeight A x v))

toOrdinaryScale : ∀ {A} (C : VacuumChart A) (a : L.Scalar (F.vacuum A))
  (u : L.Vector (F.sector A)) (x : H.X6) →
  toOrdinary C (L._·_ (F.sector A) (F.toSectorScalar A a) u) x ≡
  L._·_ (ordinary C) (scalarToOrdinary C a) (toOrdinary C u x)
toOrdinaryScale {A} C a u x =
  trans (cong (encode C) (F.recoverScale A x a u))
        (encodeScale C a (F.recoverWeight A x u))

-- Source and target are explicitly indexed by the SAME literal source.
record PhaseEndpoint (S : Z.LiteralLinearNormalizerSource) (p : I.CentralPhase3) : Set₁ where
  field
    restriction : Z.LiteralLinearPhaseRestriction S p
    frame : F.ActualLinearWeightFrame
    frameIsLiteralPhase : F.sector frame ≡ Z.phaseLinearCarrier restriction
    chart : VacuumChart frame

open PhaseEndpoint public

-- The actual phase-changing map is derived from the literal original
-- action. No independent negative action or basis permutation supplied.
literalInverter : ∀ {S p}
  (A : PhaseEndpoint S p) (B : PhaseEndpoint S (I.invertPhase p)) →
  I.CentralInverter (Z.literalNormalizerAction S) →
  L.Vector (F.sector (frame A)) → L.Vector (F.sector (frame B))
literalInverter {S} {p} A B g w =
  subst L.Vector (sym (frameIsLiteralPhase B))
    (subst (λ X → X) (sym (Z.phaseVectorIsEigenspace (restriction B)))
      (I.inverterSwapsPhase (Z.literalNormalizerAction S) p g
        (subst (λ X → X) (Z.phaseVectorIsEigenspace (restriction A))
          (subst L.Vector (frameIsLiteralPhase A) w))))

ordinaryArrow : ∀ {A B} (C : VacuumChart A) (D : VacuumChart B) →
  (L.Vector (F.sector A) → L.Vector (F.sector B)) →
  Coordinates C → Coordinates D
ordinaryArrow C D g u = toOrdinary D (g (fromOrdinary C u))

arrowIntertwines : ∀ {A B} (C : VacuumChart A) (D : VacuumChart B)
  (g : L.Vector (F.sector A) → L.Vector (F.sector B)) (w : L.Vector (F.sector A))
  (x : H.X6) →
  ordinaryArrow C D g (toOrdinary C w) x ≡ toOrdinary D (g w) x
arrowIntertwines C D g w x =
  cong (λ v → toOrdinary D (g v) x) (fromAfterTo C w)

arrowRoundtrip : ∀ {A B} (C : VacuumChart A) (D : VacuumChart B)
  (g : L.Vector (F.sector A) → L.Vector (F.sector B))
  (h : L.Vector (F.sector B) → L.Vector (F.sector A)) →
  (∀ w → h (g w) ≡ w) → (u : Coordinates C) (x : H.X6) →
  ordinaryArrow D C h (ordinaryArrow C D g u) x ≡ u x
arrowRoundtrip C D g h hg u x =
  trans (arrowIntertwines D C h (g (fromOrdinary C u)) x)
    (trans (cong (λ v → toOrdinary C v x) (hg (fromOrdinary C u)))
           (toAfterFrom C u x))

literalSignedArrow : ∀ {S p}
  (A : PhaseEndpoint S p) (B : PhaseEndpoint S (I.invertPhase p)) →
  I.CentralInverter (Z.literalNormalizerAction S) →
  Coordinates (chart A) → Coordinates (chart B)
literalSignedArrow A B g =
  ordinaryArrow (chart A) (chart B) (literalInverter A B g)

-- Reverse-solve the negative gauge at the level of maps. This is the
-- same signed formula C_actual f_+ C_source^-1 as in the Lean owner.
-- The retained reverse outer square still requires the C² residual.
negativeGauge : ∀ {P M S T : Set} →
  (P → S) → (M → P) → (S → T) → M → T
negativeGauge f sourceBack actualForward y = actualForward (f (sourceBack y))

negativeGaugeSquare : ∀ {P M S T : Set}
  (f : P → S) (sourceForward : P → M) (sourceBack : M → P)
  (actualForward : S → T) →
  (∀ x → sourceBack (sourceForward x) ≡ x) → (x : P) →
  negativeGauge f sourceBack actualForward (sourceForward x) ≡ actualForward (f x)
negativeGaugeSquare f sourceForward sourceBack actualForward inv x =
  cong (λ v → actualForward (f v)) (inv x)
