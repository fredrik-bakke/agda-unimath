# Generalized Hedberg's theorem

```agda
module foundation.generalized-hedbergs-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation.inhabited-types
open import foundation.action-on-identifications-functions
open import foundation.weakly-constant-maps
open import foundation.logical-equivalences
open import foundation-core.sections
open import foundation.propositional-truncations
open import foundation-core.function-types
```

</details>

## Idea

The {{#concept "Generalized Hedberg's theorem"}} {{#cite KECA17}} states that,
for a type `A`, the following conditions are
[equivalent](foundation.logical-equivalences.md)
[propositions](foundation-core.propositions.md):

1. The type `A` is a [set](foundation-core.sets.md).
2. The identity types of `A` have
   [split support](foundation.types-with-split-support.md).
3. The identity types of `A` have
   [weakly constant endomaps](foundation.weakly-constant-endomaps.md).

## Theorem

### The based generalized Hedberg's theorem

Given a type `A` and an element `x₀ : A`, then the following are logically
equivalent:

1. The type `x₀ ＝ x₀` is in `𝒫`.
2. For all `y : A`, the identity type `x₀ ＝ y` is in `𝒫`.
3. There is a family of `𝒫`-types `Q : A → 𝒫` such that we have an element of
   `Q x₀` and there is a map `(y : A) → Q y → x₀ ＝ y`.
4. ? There is a family of `𝒫`-types `Q : A → 𝒫` and a map
   `(y : A) → x₀ ＝ y → Q y`.
5. For all `y : A`, the identity type `x₀ ＝ y` has split `𝒫`-support.

This is a generalization of Theorem 3.11 in {{#cite KECA17}} and Theorem 3.2.1
in {{#cite Kraus15}}.

```agda

```

### The generalized Hedberg's theorem

Given a type `A`, following conditions are equivalent

1. `A` is `𝒫`-separated.
2. The identity types of `A` have split `𝒫`-support.
3. There is a reflexive binary family of `𝒫`-types `Q : A → A → 𝒫`.

## References

{{#bibliography}}

## See also

- Hedberg's theorem is formalized in
  [`foundation.decidable-equality`](foundation.decidable-equality.md).

## External links

- [Generalizations of Hedberg's Theorem](https://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html),
  formalization in Agda authored by Thorsten Altenkirch, Thierry Coquand, Martin
  Escardo, and Nicolai Kraus
