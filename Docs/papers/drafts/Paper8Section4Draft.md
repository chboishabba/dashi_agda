# Section 4 Draft: The Fermion Count 48

This section records the finite matter-count bookkeeping supplied by the
carrier.  The claim is exact at the level of Weyl-field count: the accounting
reproduces the `48` Weyl fermions obtained from three generations of quarks
and leptons when a right-handed neutrino is included in each lepton
generation.  It is not a derivation of the full Standard Model representation
content.

For one quark generation and one colour, the weak doublet contributes two Weyl
fields

```text
Q_L = (u_L, d_L).
```

The same generation and colour also has two right-handed singlet entries

```text
u_R, d_R.
```

Thus one quark generation per colour contributes

```text
2 doublet entries + 2 singlet entries = 4 Weyl fields.
```

With three colours and three generations, the quark contribution is

```text
3 colours * 3 generations * 4 Weyl fields
  = 3 * 3 * 4
  = 36 Weyl fields.
```

For one lepton generation, the weak doublet contributes two Weyl fields

```text
L_L = (nu_L, e_L).
```

The same generation also has two right-handed singlet entries, including the
right-handed neutrino

```text
e_R, nu_R.
```

Thus one lepton generation contributes

```text
2 doublet entries + 2 singlet entries = 4 Weyl fields.
```

With three generations and no colour multiplicity, the lepton contribution is

```text
3 generations * 4 Weyl fields
  = 3 * 4
  = 12 Weyl fields.
```

The total fermion count is therefore

```text
3 * 3 * 4 + 3 * 4 = 36 + 12 = 48 Weyl fields.
```

The right-handed neutrino is structurally required for this count.  Without
`nu_R`, one lepton generation would contribute only `3` Weyl fields, the
three-generation lepton total would be `9`, and the combined count would be
`36 + 9 = 45`, not `48`.

This is a count-level match only.  It does not derive the physical existence or
mass scale of right-handed neutrinos, a seesaw mechanism, anomaly
cancellation, hypercharge normalisation, Yukawa matrices, CKM/PMNS mixing,
or the full representation assignment.  The result established here is the
exact finite count `48`, with `nu_R` required by the structure of that count.
