# Quasiidempotent maps

```agda
module foundation.quasiidempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.preidempotent-maps
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A {{#concept "quasiidempotent map" Agda=is-quasiidempotent-map}} is a map
`f : A → A` [equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `I : f ∘ f ~ f` and a second-order
coherence `f ·l I ~ I ·r f`.

## Definitions

### The structure on maps of quasiidempotence

```agda
coherence-is-quasiidempotent-map :
  {l : Level} {A : UU l} (f : A → A) (I : f ∘ f ~ f) → UU l
coherence-is-quasiidempotent-map f I = f ·l I ~ I ·r f

is-quasiidempotent-map : {l : Level} {A : UU l} → (A → A) → UU l
is-quasiidempotent-map f = Σ (f ∘ f ~ f) (coherence-is-quasiidempotent-map f)

module _
  {l : Level} {A : UU l} {f : A → A} (H : is-quasiidempotent-map f)
  where

  is-preidempotent-is-quasiidempotent-map : is-preidempotent-map f
  is-preidempotent-is-quasiidempotent-map = pr1 H

  coh-is-quasiidempotent-map :
    coherence-is-quasiidempotent-map f is-preidempotent-is-quasiidempotent-map
  coh-is-quasiidempotent-map = pr2 H
```

### The type of quasiidempotent maps

```agda
quasiidempotent-map : {l : Level} (A : UU l) → UU l
quasiidempotent-map A = Σ (A → A) (is-quasiidempotent-map)

module _
  {l : Level} {A : UU l} (H : quasiidempotent-map A)
  where

  map-quasiidempotent-map : A → A
  map-quasiidempotent-map = pr1 H

  is-quasiidempotent-quasiidempotent-map :
    is-quasiidempotent-map map-quasiidempotent-map
  is-quasiidempotent-quasiidempotent-map = pr2 H

  is-preidempotent-quasiidempotent-map :
    is-preidempotent-map map-quasiidempotent-map
  is-preidempotent-quasiidempotent-map =
    is-preidempotent-is-quasiidempotent-map
      ( is-quasiidempotent-quasiidempotent-map)

  coh-quasiidempotent-map :
    coherence-is-quasiidempotent-map
      ( map-quasiidempotent-map)
      ( is-preidempotent-quasiidempotent-map)
  coh-quasiidempotent-map =
    coh-is-quasiidempotent-map is-quasiidempotent-quasiidempotent-map

  preidempotent-map-quasiidempotent-map : preidempotent-map A
  preidempotent-map-quasiidempotent-map =
    ( map-quasiidempotent-map , is-preidempotent-quasiidempotent-map)
```

## Properties

### Being quasiidempotent over a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-coherence-is-quasiidempotent-map-is-set :
    (I : f ∘ f ~ f) → is-prop (coherence-is-quasiidempotent-map f I)
  is-prop-coherence-is-quasiidempotent-map-is-set I =
    is-prop-Π
      ( λ x →
        is-set-is-prop
          ( is-set-A ((f ∘ f ∘ f) x) ((f ∘ f) x))
          ( (f ·l I) x)
          ( (I ·r f) x))

  is-prop-is-quasiidempotent-map-is-set : is-prop (is-quasiidempotent-map f)
  is-prop-is-quasiidempotent-map-is-set =
    is-prop-Σ
      ( is-prop-is-preidempotent-map-is-set is-set-A f)
      ( is-prop-coherence-is-quasiidempotent-map-is-set)

  is-quasiidempotent-map-is-set-Prop : Prop l
  is-quasiidempotent-map-is-set-Prop =
    ( is-quasiidempotent-map f , is-prop-is-quasiidempotent-map-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-quasiidempotent-map-Set : is-prop (is-quasiidempotent-map f)
  is-prop-is-quasiidempotent-map-Set =
    is-prop-is-quasiidempotent-map-is-set (is-set-type-Set A) f

  is-quasiidempotent-map-prop-Set : Prop l
  is-quasiidempotent-map-prop-Set =
    ( is-quasiidempotent-map f , is-prop-is-quasiidempotent-map-Set)
```

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
