# Localizations at subuniverses

```agda
module orthogonal-factorization-systems.localizations-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

Let `P` be a [subuniverse](foundation.subuniverses.md). Given a type `X`, its
**localization** at `P`, or **`P`-localization**, is a type `PX` in `P` and a
map `η : X → PX` such that every type in `P` is
`η`[-local](orthogonal-factorization-systems.local-types.md). I.e. for every `Z`
in `P`, the [precomposition map](foundation-core.function-types.md)

```text
  _∘ η : (PX → Z) → (X → Z)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

### The predicate of being a localization at a subuniverse

```agda
is-localization-subuniverse :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) →
  UU l2 → type-subuniverse P → UU (lsuc l1 ⊔ l2 ⊔ lP)
is-localization-subuniverse {l1} {l2} P X PX =
  ( Σ ( X → inclusion-subuniverse P PX)
      ( λ η → (Z : UU l1) → is-in-subuniverse P Z → is-local η Z))
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP)
  {X : UU l2} (PX : type-subuniverse P)
  (is-localization-PX : is-localization-subuniverse P X PX)
  where

  unit-is-localization-subuniverse : X → inclusion-subuniverse P PX
  unit-is-localization-subuniverse = pr1 is-localization-PX

  is-local-at-unit-is-in-subuniverse-is-localization-subuniverse :
    (Z : UU l1) → is-in-subuniverse P Z →
    is-local unit-is-localization-subuniverse Z
  is-local-at-unit-is-in-subuniverse-is-localization-subuniverse =
    pr2 is-localization-PX
```

### The type of localizations at a subuniverse

```agda
localization-subuniverse :
  {l1 l2 lP : Level} (P : subuniverse l1 lP) → UU l2 → UU (lsuc l1 ⊔ l2 ⊔ lP)
localization-subuniverse {l1} P X =
  Σ (type-subuniverse P) (is-localization-subuniverse P X)
```

```agda
module _
  {l1 l2 lP : Level} (P : subuniverse l1 lP)
  {X : UU l2} (L : localization-subuniverse P X)
  where

  type-subuniverse-localization-subuniverse : type-subuniverse P
  type-subuniverse-localization-subuniverse = pr1 L

  type-localization-subuniverse : UU l1
  type-localization-subuniverse =
    inclusion-subuniverse P type-subuniverse-localization-subuniverse

  is-localization-subuniverse-localization-subuniverse :
    is-localization-subuniverse P X type-subuniverse-localization-subuniverse
  is-localization-subuniverse-localization-subuniverse = pr2 L

  unit-localization-subuniverse : X → type-localization-subuniverse
  unit-localization-subuniverse =
    unit-is-localization-subuniverse P
      ( type-subuniverse-localization-subuniverse)
      ( is-localization-subuniverse-localization-subuniverse)

  is-local-at-unit-is-in-subuniverse-localization-subuniverse :
    (Z : UU l1) →
    is-in-subuniverse P Z → is-local unit-localization-subuniverse Z
  is-local-at-unit-is-in-subuniverse-localization-subuniverse =
    is-local-at-unit-is-in-subuniverse-is-localization-subuniverse P
      ( type-subuniverse-localization-subuniverse)
      ( is-localization-subuniverse-localization-subuniverse)
```

## Properties

### There is at most one `P`-localization

This is Proposition 5.1.2 in _Classifying Types_ {{#cite Rij19}} and remains to
be formalized.

## See also

- [Localizations at maps](orthogonal-factorization-systems.localizations-maps.md)

## References

{{#bibliography}} {{#reference RSS20}} {{#reference Rij19}}
