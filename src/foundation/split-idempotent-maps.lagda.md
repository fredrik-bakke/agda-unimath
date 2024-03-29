# Split idempotent maps

```agda
module foundation.split-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.preidempotent-maps
open import foundation.fixed-points-endofunctions
open import foundation.quasiidempotent-maps
open import foundation.retracts-of-types
open import foundation.universe-levels
open import foundation.weakly-constant-maps
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → A` is
{{#concept "split idempotent" Agda=is-split-idempotent-map}} if there exists a
type `B` and an inclusion-retraction pair `r`, `i` displaying `B` as a
[retract](foundation-core.retracts-of-types.md) such that `i ∘ r ~ f`. In other
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

  splitting-type-is-split-idempotent-map : UU l2
  splitting-type-is-split-idempotent-map = pr1 H

  retract-is-split-idempotent-map :
    splitting-type-is-split-idempotent-map retract-of A
  retract-is-split-idempotent-map = pr1 (pr2 H)

  inclusion-is-split-idempotent-map : splitting-type-is-split-idempotent-map → A
  inclusion-is-split-idempotent-map =
    inclusion-retract retract-is-split-idempotent-map

  map-retraction-is-split-idempotent-map :
    A → splitting-type-is-split-idempotent-map
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

  splitting-type-split-idempotent-map : UU l2
  splitting-type-split-idempotent-map =
    splitting-type-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  retract-split-idempotent-map :
    splitting-type-split-idempotent-map retract-of A
  retract-split-idempotent-map =
    retract-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  inclusion-split-idempotent-map : splitting-type-split-idempotent-map → A
  inclusion-split-idempotent-map =
    inclusion-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  map-retraction-split-idempotent-map : A → splitting-type-split-idempotent-map
  map-retraction-split-idempotent-map =
    map-retraction-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  retraction-split-idempotent-map : retraction inclusion-split-idempotent-map
  retraction-split-idempotent-map =
    retraction-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  is-retraction-map-retraction-split-idempotent-map :
    is-retraction
      ( inclusion-split-idempotent-map)
      ( map-retraction-split-idempotent-map)
  is-retraction-map-retraction-split-idempotent-map =
    is-retraction-map-retraction-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  htpy-split-idempotent-map :
    inclusion-split-idempotent-map ∘ map-retraction-split-idempotent-map ~
    map-split-idempotent-map
  htpy-split-idempotent-map =
    htpy-is-split-idempotent-map is-split-idempotent-split-idempotent-map
```

## Properties

### The splitting type of a split idempotent map is essentially unique

This is Lemma 3.4 in {{#cite Shu17}}.

```agda
module _
  {l1 : Level} {A : UU l1} {f : A → A}
  where

  map-essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    splitting-type-is-split-idempotent-map H →
    splitting-type-is-split-idempotent-map H'
  map-essentially-unique-splitting-type-is-split-idempotent-map H H' =
    map-retraction-is-split-idempotent-map H' ∘
    inclusion-is-split-idempotent-map H

  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map' :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    is-section
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H H')
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H' H)
  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
    H H' =
    ( map-retraction-is-split-idempotent-map H' ·l
      ( ( htpy-is-split-idempotent-map H) ∙h
        ( inv-htpy (htpy-is-split-idempotent-map H'))) ·r
      inclusion-is-split-idempotent-map H') ∙h
    ( horizontal-concat-htpy
      ( is-retraction-map-retraction-is-split-idempotent-map H')
      ( is-retraction-map-retraction-is-split-idempotent-map H'))

  is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    is-equiv
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H H')
  is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map H H' =
    is-equiv-is-invertible
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H' H)
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
        ( H)
        ( H'))
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
        ( H')
        ( H))

  essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    splitting-type-is-split-idempotent-map H ≃
    splitting-type-is-split-idempotent-map H'
  essentially-unique-splitting-type-is-split-idempotent-map H H' =
    ( map-essentially-unique-splitting-type-is-split-idempotent-map H H' ,
      is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map
        ( H)
        ( H'))
```

### Split idempotent maps are preidempotent

This is Lemma 3.3 in {{#cite Shu17}}.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  is-preidempotent-is-split-idempotent-map : is-preidempotent-map f
  is-preidempotent-is-split-idempotent-map =
    is-preidempotent-map-inv-htpy
      ( is-preidempotent-inclusion-retraction
        ( inclusion-is-split-idempotent-map H)
        ( map-retraction-is-split-idempotent-map H)
        ( is-retraction-map-retraction-is-split-idempotent-map H))
      ( htpy-is-split-idempotent-map H)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  is-preidempotent-split-idempotent-map :
    is-preidempotent-map (map-split-idempotent-map H)
  is-preidempotent-split-idempotent-map =
    is-preidempotent-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map H)
```

### Split idempotent maps are quasiidempotent

This is Lemma 3.6 in {{#cite Shu17}}, and remains to be formalized.

```text
module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  coherence-is-quasiidempotent-is-split-idempotent-map :
    coherence-is-quasiidempotent-map f
      ( is-preidempotent-is-split-idempotent-map H)
  coherence-is-quasiidempotent-is-split-idempotent-map =

  is-quasiidempotent-is-split-idempotent-map : is-quasiidempotent-map f
  is-quasiidempotent-is-split-idempotent-map =
    ( is-preidempotent-is-split-idempotent-map H ,
      coherence-is-quasiidempotent-is-split-idempotent-map)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  is-quasiidempotent-split-idempotent-map :
    is-quasiidempotent-map (map-split-idempotent-map H)
  is-quasiidempotent-split-idempotent-map =
    is-quasiidempotent-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map H)
```

### Every preidempotent on a set splits

This is Theorem 3.7 of {{#cite Shu17}}.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (is-set-A : is-set A) (H : is-preidempotent-map f)
  where

  splitting-type-is-split-idempotent-is-preidempotent-map-is-set : UU l
  splitting-type-is-split-idempotent-is-preidempotent-map-is-set =
    fixed-point f

  inclusion-is-split-idempotent-is-preidempotent-map-is-set :
    fixed-point f → A
  inclusion-is-split-idempotent-is-preidempotent-map-is-set = pr1

  map-retraction-is-split-idempotent-is-preidempotent-map-is-set :
    A → fixed-point f
  map-retraction-is-split-idempotent-is-preidempotent-map-is-set x = (f x , H x)

  is-retraction-map-retraction-is-split-idempotent-is-preidempotent-map-is-set :
    is-retraction
      ( inclusion-is-split-idempotent-is-preidempotent-map-is-set)
      ( map-retraction-is-split-idempotent-is-preidempotent-map-is-set)
  is-retraction-map-retraction-is-split-idempotent-is-preidempotent-map-is-set
    (x , p) =
    eq-pair-Σ p (eq-is-prop (is-set-A (f x) x))

  retraction-is-split-idempotent-is-preidempotent-map-is-set :
    retraction (inclusion-is-split-idempotent-is-preidempotent-map-is-set)
  retraction-is-split-idempotent-is-preidempotent-map-is-set =
    ( map-retraction-is-split-idempotent-is-preidempotent-map-is-set ,
      is-retraction-map-retraction-is-split-idempotent-is-preidempotent-map-is-set)

  retract-is-split-idempotent-is-preidempotent-map-is-set :
    splitting-type-is-split-idempotent-is-preidempotent-map-is-set retract-of A
  retract-is-split-idempotent-is-preidempotent-map-is-set =
    ( inclusion-is-split-idempotent-is-preidempotent-map-is-set ,
      retraction-is-split-idempotent-is-preidempotent-map-is-set)

  htpy-is-split-idempotent-is-preidempotent-map-is-set :
    inclusion-is-split-idempotent-is-preidempotent-map-is-set ∘
    map-retraction-is-split-idempotent-is-preidempotent-map-is-set ~
    f
  htpy-is-split-idempotent-is-preidempotent-map-is-set = refl-htpy

  is-split-idempotent-is-preidempotent-map-is-set : is-split-idempotent-map l f
  is-split-idempotent-is-preidempotent-map-is-set =
    ( splitting-type-is-split-idempotent-is-preidempotent-map-is-set ,
      retract-is-split-idempotent-is-preidempotent-map-is-set ,
      htpy-is-split-idempotent-is-preidempotent-map-is-set)
```

### Weakly constant preidempotent maps split

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (H : is-preidempotent-map f) (W : is-weakly-constant-map f)
  where

  splitting-type-is-split-idempotent-is-weakly-constant-is-preidempotent-map : UU l
  splitting-type-is-split-idempotent-is-weakly-constant-is-preidempotent-map =
    fixed-point f

  inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    fixed-point f → A
  inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map = pr1

  map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    A → fixed-point f
  map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map x = (f x , H x)

  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    is-retraction
      ( inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map)
      ( map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map)
  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map
    _ =
    eq-is-prop (is-prop-fixed-point-is-weakly-constant-map W)

  retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    retraction (inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map)
  retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map =
    ( map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map ,
      is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map)

  retract-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    splitting-type-is-split-idempotent-is-weakly-constant-is-preidempotent-map retract-of A
  retract-is-split-idempotent-is-weakly-constant-is-preidempotent-map =
    ( inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map ,
      retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map)

  htpy-is-split-idempotent-is-weakly-constant-is-preidempotent-map :
    inclusion-is-split-idempotent-is-weakly-constant-is-preidempotent-map ∘
    map-retraction-is-split-idempotent-is-weakly-constant-is-preidempotent-map ~
    f
  htpy-is-split-idempotent-is-weakly-constant-is-preidempotent-map = refl-htpy

  is-split-idempotent-is-weakly-constant-is-preidempotent-map : is-split-idempotent-map l f
  is-split-idempotent-is-weakly-constant-is-preidempotent-map =
    ( splitting-type-is-split-idempotent-is-weakly-constant-is-preidempotent-map ,
      retract-is-split-idempotent-is-weakly-constant-is-preidempotent-map ,
      htpy-is-split-idempotent-is-weakly-constant-is-preidempotent-map)
```

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
