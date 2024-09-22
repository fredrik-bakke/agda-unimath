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

Let `𝒫` be a [subuniverse](foundation.subuniverses.md). Given a type `X`, its
**localization** at `𝒫`, or **`𝒫`-localization**, is a type `PX` in `𝒫` and a
map `η : X → PX` such that every type in `𝒫` is
`η`[-local](orthogonal-factorization-systems.local-types.md). I.e. for every `Y`
in `𝒫`, the [precomposition map](foundation-core.function-types.md)

```text
  _∘ η : (PX → Y) → (X → Y)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

### The predicate of being a localization at a subuniverse

```agda
is-subuniverse-localization :
  {l1 l2 lP : Level} (𝒫 : subuniverse l1 lP) →
  UU l2 → UU l1 → UU (lsuc l1 ⊔ l2 ⊔ lP)
is-subuniverse-localization {l1} {l2} 𝒫 X PX =
  ( is-in-subuniverse 𝒫 PX) ×
  ( Σ ( X → PX)
      ( λ η → (Y : UU l1) → is-in-subuniverse 𝒫 Y → is-local η Y))
```

```agda
module _
  {l1 l2 lP : Level} (𝒫 : subuniverse l1 lP) {X : UU l2} {PX : UU l1}
  (is-localization-PX : is-subuniverse-localization 𝒫 X PX)
  where

  is-in-subuniverse-is-subuniverse-localization : is-in-subuniverse 𝒫 PX
  is-in-subuniverse-is-subuniverse-localization = pr1 is-localization-PX

  unit-is-subuniverse-localization : X → PX
  unit-is-subuniverse-localization = pr1 (pr2 is-localization-PX)

  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization :
    (Y : UU l1) → is-in-subuniverse 𝒫 Y →
    is-local unit-is-subuniverse-localization Y
  is-local-at-unit-is-in-subuniverse-is-subuniverse-localization =
    pr2 (pr2 is-localization-PX)
```

### The type of localizations at a subuniverse

```agda
subuniverse-localization :
  {l1 l2 lP : Level} (𝒫 : subuniverse l1 lP) → UU l2 → UU (lsuc l1 ⊔ l2 ⊔ lP)
subuniverse-localization {l1} 𝒫 X = Σ (UU l1) (is-subuniverse-localization 𝒫 X)
```

```agda
module _
  {l1 l2 lP : Level} (𝒫 : subuniverse l1 lP)
  {X : UU l2} (L : subuniverse-localization 𝒫 X)
  where

  type-subuniverse-localization : UU l1
  type-subuniverse-localization = pr1 L

  is-subuniverse-localization-subuniverse-localization :
    is-subuniverse-localization 𝒫 X type-subuniverse-localization
  is-subuniverse-localization-subuniverse-localization = pr2 L

  is-in-subuniverse-subuniverse-localization :
    is-in-subuniverse 𝒫 type-subuniverse-localization
  is-in-subuniverse-subuniverse-localization =
    is-in-subuniverse-is-subuniverse-localization 𝒫
      ( is-subuniverse-localization-subuniverse-localization)

  unit-subuniverse-localization : X → type-subuniverse-localization
  unit-subuniverse-localization =
    unit-is-subuniverse-localization 𝒫
      ( is-subuniverse-localization-subuniverse-localization)

  is-local-at-unit-is-in-subuniverse-subuniverse-localization :
    (Y : UU l1) →
    is-in-subuniverse 𝒫 Y → is-local unit-subuniverse-localization Y
  is-local-at-unit-is-in-subuniverse-subuniverse-localization =
    is-local-at-unit-is-in-subuniverse-is-subuniverse-localization 𝒫
      ( is-subuniverse-localization-subuniverse-localization)
```

## Properties

### There is at most one `𝒫`-localization

This is Proposition 5.1.2 in _Classifying Types_, and remains to be formalized.

## See also

- [Reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)
  are subuniverses that have all localizations.

- [Localizations at maps](orthogonal-factorization-systems.localizations-maps.md)

## References

{{#bibliography}} {{#reference RSS20}} {{#reference Rij19}}
