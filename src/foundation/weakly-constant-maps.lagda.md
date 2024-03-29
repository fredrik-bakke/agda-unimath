# Weakly constant maps

```agda
module foundation.weakly-constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "weakly constant" Disambiguation="map of types" Agda=is-weakly-constant-map}}
if any two elements in `A` are mapped to
[identical elements](foundation-core.identity-types.md) in `B`.

## Definition

```agda
is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → f x ＝ f y
```

## Properties

### Being weakly constant is a property if the codomain is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B)
  where

  abstract
    is-prop-is-weakly-constant-map-Set : is-prop (is-weakly-constant-map f)
    is-prop-is-weakly-constant-map-Set =
      is-prop-iterated-Π 2 (λ x y → is-set-type-Set B (f x) (f y))

  is-weakly-constant-map-prop-Set : Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-map-prop-Set = is-weakly-constant-map f
  pr2 is-weakly-constant-map-prop-Set = is-prop-is-weakly-constant-map-Set
```

## References

{{#bibliography}} {{#reference KECA17}}
