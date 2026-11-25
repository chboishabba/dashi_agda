module DASHI.Moonshine.Monster3BActualLinearWeightFrameExact where

-- Successor of the finite basis recognition and Cartesian pure-pair contract.
-- A full linear vector has ALL X6 coordinates, not one selected weight label.
-- The source supplies the actual linear carriers, translations/projectors and
-- finite-sum laws. Both inverse laws are derived (pointwise on the coordinates).
-- No actual Conway representation is manufactured by this record.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

sameTrit : Trit → Trit → Bool
sameTrit neg neg = true
sameTrit zer zer = true
sameTrit pos pos = true
sameTrit _ _ = false

and : Bool → Bool → Bool
and true b = b
and false b = false

sameWeight : H.X6 → H.X6 → Bool
sameWeight x y =
  and (sameTrit (H.x0 x) (H.x0 y))
  (and (sameTrit (H.x1 x) (H.x1 y))
  (and (sameTrit (H.x2 x) (H.x2 y))
  (and (sameTrit (H.x3 x) (H.x3 y))
  (and (sameTrit (H.x4 x) (H.x4 y))
       (sameTrit (H.x5 x) (H.x5 y))))))

delta : {A : Set} → A → H.X6 → H.X6 → A → A
delta zero x y u with sameWeight x y
... | true = u
... | false = zero

record ActualLinearWeightFrame : Set₁ where
  field
    sector vacuum : Linear.HilbertLift
    toSectorScalar : Linear.Scalar vacuum → Linear.Scalar sector
    includeWeight : H.X6 → Linear.Vector vacuum → Linear.Vector sector
    recoverWeight : H.X6 → Linear.Vector sector → Linear.Vector vacuum
    sumSector : (H.X6 → Linear.Vector sector) → Linear.Vector sector
    sumVacuum : (H.X6 → Linear.Vector vacuum) → Linear.Vector vacuum

    includeAdd : ∀ x u v →
      includeWeight x (Linear._+_ vacuum u v) ≡
      Linear._+_ sector (includeWeight x u) (includeWeight x v)
    includeScale : ∀ x a u →
      includeWeight x (Linear._·_ vacuum a u) ≡
      Linear._·_ sector (toSectorScalar a) (includeWeight x u)
    recoverAdd : ∀ x u v →
      recoverWeight x (Linear._+_ sector u v) ≡
      Linear._+_ vacuum (recoverWeight x u) (recoverWeight x v)
    recoverScale : ∀ x a w →
      recoverWeight x (Linear._·_ sector (toSectorScalar a) w) ≡
      Linear._·_ vacuum a (recoverWeight x w)

    sumSectorCong : ∀ f g → (∀ x → f x ≡ g x) → sumSector f ≡ sumSector g
    sumVacuumCong : ∀ f g → (∀ x → f x ≡ g x) → sumVacuum f ≡ sumVacuum g
    sumSectorAdd : ∀ f g →
      sumSector (λ x → Linear._+_ sector (f x) (g x)) ≡
      Linear._+_ sector (sumSector f) (sumSector g)
    sumSectorScale : ∀ a f →
      sumSector (λ x → Linear._·_ sector (toSectorScalar a) (f x)) ≡
      Linear._·_ sector (toSectorScalar a) (sumSector f)

    recoverSum : ∀ x f →
      recoverWeight x (sumSector f) ≡ sumVacuum (λ y → recoverWeight x (f y))
    orthogonal : ∀ x y u →
      recoverWeight x (includeWeight y u) ≡ delta (Linear.zero vacuum) x y u
    sumDelta : ∀ x f →
      sumVacuum (λ y → delta (Linear.zero vacuum) x y (f y)) ≡ f x
    complete : ∀ w → sumSector (λ x → includeWeight x (recoverWeight x w)) ≡ w

open ActualLinearWeightFrame public

Coordinates : ActualLinearWeightFrame → Set
Coordinates F = H.X6 → Linear.Vector (vacuum F)

evaluate : (F : ActualLinearWeightFrame) → Coordinates F → Linear.Vector (sector F)
evaluate F u = sumSector F (λ x → includeWeight F x (u x))

recover : (F : ActualLinearWeightFrame) → Linear.Vector (sector F) → Coordinates F
recover F w x = recoverWeight F x w

recoverAfterEvaluate : (F : ActualLinearWeightFrame) (u : Coordinates F) (x : H.X6) →
  recover F (evaluate F u) x ≡ u x
recoverAfterEvaluate F u x =
  trans (recoverSum F x (λ y → includeWeight F y (u y)))
    (trans (sumVacuumCong F _ _ (λ y → orthogonal F x y (u y)))
           (sumDelta F x u))

evaluateAfterRecover : (F : ActualLinearWeightFrame) (w : Linear.Vector (sector F)) →
  evaluate F (recover F w) ≡ w
evaluateAfterRecover F = complete F

evaluateAdd : (F : ActualLinearWeightFrame) (u v : Coordinates F) →
  evaluate F (λ x → Linear._+_ (vacuum F) (u x) (v x)) ≡
  Linear._+_ (sector F) (evaluate F u) (evaluate F v)
evaluateAdd F u v =
  trans (sumSectorCong F _ _ (λ x → includeAdd F x (u x) (v x)))
        (sumSectorAdd F (λ x → includeWeight F x (u x)) (λ x → includeWeight F x (v x)))

evaluateScale : (F : ActualLinearWeightFrame) (a : Linear.Scalar (vacuum F)) (u : Coordinates F) →
  evaluate F (λ x → Linear._·_ (vacuum F) a (u x)) ≡
  Linear._·_ (sector F) (toSectorScalar F a) (evaluate F u)
evaluateScale F a u =
  trans (sumSectorCong F _ _ (λ x → includeScale F x a (u x)))
        (sumSectorScale F a (λ x → includeWeight F x (u x)))

-- A signed arrow may change the sector. Its source and target are explicit.
transport : (F G : ActualLinearWeightFrame) →
  (Linear.Vector (sector F) → Linear.Vector (sector G)) → Coordinates F → Coordinates G
transport F G g u = recover G (g (evaluate F u))

transportIntertwines : (F G : ActualLinearWeightFrame)
  (g : Linear.Vector (sector F) → Linear.Vector (sector G)) (u : Coordinates F) →
  evaluate G (transport F G g u) ≡ g (evaluate F u)
transportIntertwines F G g u = evaluateAfterRecover G (g (evaluate F u))

transportRoundtrip : (F G : ActualLinearWeightFrame)
  (g : Linear.Vector (sector F) → Linear.Vector (sector G))
  (h : Linear.Vector (sector G) → Linear.Vector (sector F)) →
  (∀ w → h (g w) ≡ w) → (u : Coordinates F) (x : H.X6) →
  transport G F h (transport F G g u) x ≡ u x
transportRoundtrip F G g h hg u x =
  trans (cong (λ w → recover F (h w) x) (transportIntertwines F G g u))
    (trans (cong (λ w → recover F w x) (hg (evaluate F u)))
           (recoverAfterEvaluate F u x))
