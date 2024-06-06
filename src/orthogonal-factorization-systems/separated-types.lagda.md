# Separated types

```agda
module orthogonal-factorization-systems.separated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A type `A` is said to be **separated** with respect to a map `f`, or
**`f`-separated**, if its [identity types](foundation-core.identity-types.md)
are [`f`-local](orthogonal-factorization-systems.local-types.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-map-separated-family : (X → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  is-map-separated-family A = (x : X) (y z : A x) → is-local f (y ＝ z)

  is-map-separated : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  is-map-separated A = is-map-separated-family (λ _ → A)
```

## Properties

### If `f`-local types are closed under dependent sums then `f`-separated types are closed under dependent sums

This is remarked in Remark 2.16 of {{#cite CORS20}}.

### A type is `f`-separated if and only if it is local at the suspension of `f`

This is lemma 2.15 of {{#cite CORS20}}.

### The universe of `f`-separated types is `f`-separated

This is proposition 2.18 of {{#cite CORS20}}.

### If `P : X → 𝒰` is a family of `f`-local types over an `f`-separated type, then the dependent sum is `f`-separated

This is Lemma 2.21 of {{#cite CORS20}}.

## References

{{#bibliography}} {{#reference Rij19}}
