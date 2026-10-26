module DASHI.Foundations.C3NineSiteSixStepMirrorExact where

-- Six-step spatial reflection; twelve-step identity.
-- Reflects column, NOT both coordinates and not a scalar minus sign.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Foundations.C3NineSiteAlternatingOrbitExact as O

mirror : O.Site → O.Site
mirror O.TL = O.TR
mirror O.TM = O.TM
mirror O.TR = O.TL
mirror O.ML = O.MR
mirror O.MM = O.MM
mirror O.MR = O.ML
mirror O.BL = O.BR
mirror O.BM = O.BM
mirror O.BR = O.BL

mirror² : ∀ x → mirror (mirror x) ≡ x
mirror² O.TL = refl
mirror² O.TM = refl
mirror² O.TR = refl
mirror² O.ML = refl
mirror² O.MM = refl
mirror² O.MR = refl
mirror² O.BL = refl
mirror² O.BM = refl
mirror² O.BR = refl

shift6 : O.T12 → O.T12
shift6 O.t0 = O.t6
shift6 O.t1 = O.t7
shift6 O.t2 = O.t8
shift6 O.t3 = O.t9
shift6 O.t4 = O.t10
shift6 O.t5 = O.t11
shift6 O.t6 = O.t0
shift6 O.t7 = O.t1
shift6 O.t8 = O.t2
shift6 O.t9 = O.t3
shift6 O.t10 = O.t4
shift6 O.t11 = O.t5

shift6² : ∀ t → shift6 (shift6 t) ≡ t
shift6² O.t0 = refl
shift6² O.t1 = refl
shift6² O.t2 = refl
shift6² O.t3 = refl
shift6² O.t4 = refl
shift6² O.t5 = refl
shift6² O.t6 = refl
shift6² O.t7 = refl
shift6² O.t8 = refl
shift6² O.t9 = refl
shift6² O.t10 = refl
shift6² O.t11 = refl

sixStepMirror : ∀ t → O.orbit (shift6 t) ≡ mirror (O.orbit t)
sixStepMirror O.t0 = refl
sixStepMirror O.t1 = refl
sixStepMirror O.t2 = refl
sixStepMirror O.t3 = refl
sixStepMirror O.t4 = refl
sixStepMirror O.t5 = refl
sixStepMirror O.t6 = refl
sixStepMirror O.t7 = refl
sixStepMirror O.t8 = refl
sixStepMirror O.t9 = refl
sixStepMirror O.t10 = refl
sixStepMirror O.t11 = refl

-- Additional to spatial mirror: how an independently carried normal
-- or transverse frame transforms under this mirror is a separate choice.
