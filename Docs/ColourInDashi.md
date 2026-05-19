# Colour In Dashi

This note sharpens one recurring informal claim:

> Dashi does not treat colour as a primitive property. It treats colour as a
> projection-stable observable on a structured latent signal.

The note is intentionally narrow. It distinguishes three different uses of the
word "colour" and states exactly what the Dashi formalism does and does not
claim.

## 1. Split The Word "Colour"

### Optical colour

Optical colour is the observable produced by a spectral signal under a
particular observation map. In ordinary physics language this is the
sensor-facing or eye-facing colour channel.

Minimal Dashi form:

`x ∈ X`
latent spectral or field state

`y = P(x)`
observed colour signal under projection `P`

The strongest Dashi-compatible statement is:

> optical colour is a projection-stable observable, not a primitive property
> attached to the latent state by itself.

### Perceptual colour

Perceptual colour is the colour actually organized by an observer or
measurement system after sensor projection, inference, and any internal
stability rules.

In Dashi language this is one layer further than optical colour:

- optical colour: the projected observable
- perceptual colour: the organized or selected interpretation of that
  observable

This matters because Dashi can model inference or reconstruction rules without
identifying them with the projection itself.

### QCD colour

QCD colour is not optical colour. It is a gauge-theoretic internal degree of
freedom in the strong interaction.

The only safe Dashi-level analogy is structural:

- both optical colour and QCD colour are non-primitive labels living inside a
  larger state description
- both require a distinction between latent state and observable outcome

But the formal objects are different:

- optical colour is a projection problem on a signal state
- QCD colour is a non-abelian gauge degree of freedom

So Dashi should not collapse them into one concept.

## 2. Dashi Representation Layer

The natural Dashi representation is a multiscale coordinate description.

For one channel:

`x = Σ_k S_k · 3^k`

For multiple colour-like channels:

`x = (x_1, x_2, x_3, ...)`

with each component decomposed across scales.

This supports the informal statement:

> colour is represented in Dashi as structured multiscale signal coordinates,
> not as an irreducible primitive tag.

That is a representation claim, not yet a perceptual claim.

## 3. Quotient View

Let `P : X → Y` be the observation map.

Then two latent states can be observationally identical:

`x₁ ≠ x₂` but `P(x₁) = P(x₂)`

This yields the quotient-style reading:

`[x]_P = { z ∈ X | P(z) = P(x) }`

The clean Dashi statement is:

> observed optical colour belongs to a projection class.

This is the right place to connect metamerism:

- different latent spectra
- same projected colour signal

## 4. MDL Selection Is A Reconstruction Rule

Once the projection class exists, Dashi may choose a preferred representative by
description length:

`x* = argmin_{z ∈ [x]_P} L(z)`

This is useful, but it should be stated carefully.

Safe statement:

> MDL selects a preferred reconstruction of a colour class.

Unsafe statement:

> colour just is the MDL-minimal representative.

The unsafe version confuses:

- the observed colour signal
- the latent equivalence class
- the chosen reconstruction rule

So the right ordering is:

1. latent state `x`
2. projected observable `P(x)`
3. projection class `[x]_P`
4. preferred reconstruction `x*`

## 5. Geometry And Dynamics

Dashi can place extra structure on colour states.

### Ultrametric geometry

A multiscale code naturally induces an ultrametric or hierarchical similarity.

This is a good internal model for encoded colour states:

`d(x, y) = 3^{-k}`

where `k` is the first scale of disagreement.

But the correct claim boundary is:

> this is Dashi geometry on encoded states, not automatically a theorem about
> empirical human perceptual colour space.

### Cone-constrained dynamics

Dashi can also constrain colour transitions through delta-state admissibility:

`Δx = x_{t+1} - x_t`

with admissibility screened by a quadratic or cone condition such as
`Q(Δx) ≤ 0`.

Again, the safe reading is internal:

> Dashi defines admissible colour dynamics inside the model.

It is not yet a theorem of vision science or optics.

## 6. Theorem-Style Statement

The strongest compact theorem-style note supported by the current Dashi
language is:

### Projection-Stable Colour Statement

Let `X` be a latent structured signal space, `P : X → Y` a colour-observation
projection, and `L : X → ℝ` a description-length functional.

Then Dashi treats colour through the following layered objects:

1. `y = P(x)` is the observed optical colour signal.
2. `[x]_P` is the latent colour class compatible with that observation.
3. `x* = argmin_{z ∈ [x]_P} L(z)` is a preferred reconstruction rule when one is
   required.
4. additional geometry and admissibility constraints may be imposed on `X`,
   including multiscale ultrametric similarity and cone-screened delta
   dynamics.

Conclusion:

> in Dashi, colour is not primitive; it is a projection-stable observable on a
> structured latent signal, with optional MDL-based reconstruction and optional
> geometry/dynamics on the latent state space.

## 7. Not Claimed

This note does not claim:

- that human perceptual colour space is empirically ultrametric
- that cone-screened colour dynamics are a finished theory of optics or vision
- that optical colour and QCD colour are the same formal object
- that the repo already contains a dedicated Agda theorem proving a colour
  quotient theorem

## 8. Safe One-Line Summary

> In Dashi, colour is a projection-stable observable on a multiscale latent
> signal; MDL chooses preferred reconstructions, while ultrametric and cone
> structure constrain the internal state geometry and dynamics.
