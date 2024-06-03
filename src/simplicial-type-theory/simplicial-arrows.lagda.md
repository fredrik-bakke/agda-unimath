# Simplicial arrows

```agda
module simplicial-type-theory.simplicial-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
```

</details>

## Idea

A
{{#concept "simplicial arrow" Disambiguation="simplicial type theory" Agda=simplicial-arrow}}
in a type `A` is a map from the
[directed interval](simplicial-type-theory.directed-interval-type.md) to the
type, `𝟚 → A`. Given a simplicial arrow `α` in `A`, we call `α 0₂` the _source_,
and `α 1₂` the _target_ of the arrow. See
[directed edges](simplicial-type-theory.directed-edges.md) for simplicial arrows
with a specified source and target.

## Definitions

### Simplicial arrows in types dependent over the directed interval

```agda
simplicial-arrow' : {l : Level} → (𝟚 → UU l) → UU l
simplicial-arrow' A = (t : 𝟚) → A t
```

### Simplicial arrows

```agda
simplicial-arrow : {l : Level} → UU l → UU l
simplicial-arrow A = simplicial-arrow' (λ _ → A)
```

### The identity/constant simplicial arrows

```agda
id-simplicial-arrow : {l : Level} {A : UU l} (x : A) → simplicial-arrow A
id-simplicial-arrow x _ = x
```

### The representing arrow of the directed interval

```agda
representing-arrow-𝟚 : simplicial-arrow 𝟚
representing-arrow-𝟚 = id
```

### Simplicial arrows arising from equalities

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  simplicial-arrow-eq : x ＝ y → simplicial-arrow A
  simplicial-arrow-eq refl = id-simplicial-arrow x

  compute-source-simplicial-arrow-eq :
    (p : x ＝ y) → simplicial-arrow-eq p 0₂ ＝ x
  compute-source-simplicial-arrow-eq refl = refl

  compute-target-simplicial-arrow-eq :
    (p : x ＝ y) → simplicial-arrow-eq p 1₂ ＝ y
  compute-target-simplicial-arrow-eq refl = refl
```

## Properties

### The representing arrow of the directed interval is not constant

```agda
is-not-constant-representing-arrow-𝟚 :
  (t : 𝟚) → ¬ (representing-arrow-𝟚 ~ id-simplicial-arrow t)
is-not-constant-representing-arrow-𝟚 _ H = is-nontrivial-𝟚 (H 0₂ ∙ inv (H 1₂))
```