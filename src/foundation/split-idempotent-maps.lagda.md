# Split idempotent maps

```agda
module foundation.split-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → A` is
{{#concept "split idempotent" Agda=is-split-idempotent-map}} if there exists a
type `B` and an inclusion-retraction pair `r`, `i` displaying `B` as a
[retract](foundation.retracts-of-types.md) such that `i ∘ r ~ f`. In other
words, if we have a commutative diagram

```text
           f
       A ----> A
      ∧ \     ∧
   i /   \r  / i
    /     ∨ /
  B ====== B.
```

## Definitions

### The predicate on a map of being split idempotent

```agda
is-split-idempotent-map :
  {l1 : Level} (l2 : Level) {A : UU l1} → (A → A) → UU (l1 ⊔ lsuc l2)
is-split-idempotent-map l2 {A} f =
  Σ ( UU l2)
    ( λ B →
      Σ ( B retract-of A)
        ( λ R → inclusion-retract R ∘ map-retraction-retract R ~ f))

module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  type-is-split-idempotent-map : UU l2
  type-is-split-idempotent-map = pr1 H

  retract-is-split-idempotent-map : type-is-split-idempotent-map retract-of A
  retract-is-split-idempotent-map = pr1 (pr2 H)

  inclusion-is-split-idempotent-map : type-is-split-idempotent-map → A
  inclusion-is-split-idempotent-map =
    inclusion-retract retract-is-split-idempotent-map

  map-retraction-is-split-idempotent-map : A → type-is-split-idempotent-map
  map-retraction-is-split-idempotent-map =
    map-retraction-retract retract-is-split-idempotent-map

  retraction-is-split-idempotent-map :
    retraction inclusion-is-split-idempotent-map
  retraction-is-split-idempotent-map =
    retraction-retract retract-is-split-idempotent-map

  is-retraction-map-retraction-is-split-idempotent-map :
    is-retraction
      ( inclusion-is-split-idempotent-map)
      ( map-retraction-is-split-idempotent-map)
  is-retraction-map-retraction-is-split-idempotent-map =
    is-retraction-map-retraction-retract retract-is-split-idempotent-map

  htpy-is-split-idempotent-map :
    inclusion-is-split-idempotent-map ∘ map-retraction-is-split-idempotent-map ~
    f
  htpy-is-split-idempotent-map = pr2 (pr2 H)
```

### The type of split idempotent maps

```agda
split-idempotent-map : {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
split-idempotent-map l2 A = Σ (A → A) (is-split-idempotent-map l2)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  map-split-idempotent-map : A → A
  map-split-idempotent-map = pr1 H

  is-split-idempotent-split-idempotent-map :
    is-split-idempotent-map l2 map-split-idempotent-map
  is-split-idempotent-split-idempotent-map = pr2 H

  type-split-idempotent-map : UU l2
  type-split-idempotent-map =
    type-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  retract-split-idempotent-map : type-split-idempotent-map retract-of A
  retract-split-idempotent-map =
    retract-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  inclusion-split-idempotent-map : type-split-idempotent-map → A
  inclusion-split-idempotent-map =
    inclusion-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  map-retraction-split-idempotent-map : A → type-split-idempotent-map
  map-retraction-split-idempotent-map =
    map-retraction-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  retraction-split-idempotent-map : retraction inclusion-split-idempotent-map
  retraction-split-idempotent-map =
    retraction-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  is-retraction-map-retraction-split-idempotent-map :
    is-retraction
      ( inclusion-split-idempotent-map)
      ( map-retraction-split-idempotent-map)
  is-retraction-map-retraction-split-idempotent-map =
    is-retraction-map-retraction-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  htpy-split-idempotent-map :
    inclusion-split-idempotent-map ∘ map-retraction-split-idempotent-map ~
    map-split-idempotent-map
  htpy-split-idempotent-map =
    htpy-is-split-idempotent-map is-split-idempotent-split-idempotent-map
```

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
