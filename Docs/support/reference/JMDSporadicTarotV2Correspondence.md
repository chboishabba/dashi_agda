# JMD Sporadic Group + Kaballah Tarot v2 Correspondence

## Source-faithful poster transcription

The displayed v2 poster contains twenty-two Arcana slots. It assigns twenty-one actual sporadic groups and one synthetic `Co4` label:

| Arcana | Poster label |
|---|---|
| Fool | M11 |
| Magician | M12 |
| High Priestess | M22 |
| Empress | M23 |
| Emperor | M24 |
| Hierophant | Co1 |
| Lovers | Co2 |
| Chariot | Co3 |
| Strength | synthetic Co4 |
| Hermit | HS |
| Wheel of Fortune | McL |
| Justice | J1 |
| Hanged Man | J2 |
| Death | J3 |
| Temperance | J4 |
| Devil | Ru |
| Tower | Suz |
| Star | O'Nan |
| Moon | Ly |
| Sun | Th |
| Judgement | Baby Monster |
| World | Monster |

The five actual sporadic groups omitted from the poster are:

```text
Fi22, Fi23, Fi24', He, HN.
```

Therefore the source itself does not provide a total map

```text
Phi : SporadicGroup -> MajorArcana.
```

The implementation instead provides a total source-faithful partial assignment:

```text
jmdV2Assignment : SporadicGroup -> SourceFaithfulAssignment
```

where every actual sporadic group receives:

- an optional Arcana;
- assigned or omitted status;
- a source-derived rationale;
- an authority classification.

The synthetic `Co4 -> Strength` card is represented separately. It remains symbolically source-faithful while retaining the theorem that no fourth Conway sporadic referent exists.

## Exact accounting

```text
21 displayed actual sporadics
+ 5 omitted actual sporadics
= 26 actual sporadics

21 displayed actual sporadics
+ 1 synthetic Co4 card
= 22 poster cards.
```

## Completion obligation

`TotalisedCorrespondence` represents any later attempt to construct a genuine total

```text
Phi : S26 -> A22.
```

Such an object must preserve all twenty-one displayed actual-group assignments and supply explicit rationales and authorities for the five omitted groups. The poster alone does not construct this object.

## Authority boundary

The implementation does not claim:

- that `Co4` is a sporadic simple group;
- that the poster lists all twenty-six sporadics;
- that the five omitted groups can be assigned by aesthetic guesswork;
- that a symbolic correspondence proves a mathematical relationship;
- or that a total `S26 -> A22` map is already present.
