# Globular diagrams of types

```agda
module structured-types.globular-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.postcomposition-functions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "globular diagram" Disambiguation="of types" Agda=globular-diagram}}
of types `A` is a [sequence](foundation.sequences.md) of types together with
pairs of maps between every two consecutive types called the _source_ and
_target_ maps

```text
  sₙ : Aₙ₊₁ → Aₙ    and    tₙ : Aₙ₊₁ → Aₙ
```

giving a sequential diagram of parallell pairs maps that extend infinitely to
the left:

```text
      s₃        s₂        s₁        s₀
    ----->    ----->    ----->    ----->
  ⋯        A₃        A₂        A₁        A₀.
    ----->    ----->    ----->    ----->
      t₃        t₂        t₁        t₀
```

In addition, maps of a globular diagram are subject to the relations

```text
  sₙ ∘ sₙ₊₁ ~ sₙ ∘ tₙ₊₁    and    tₙ ∘ sₙ₊₁ ~ tₙ ∘ tₙ₊₁.
```

## Definitions

### Globular diagrams of types

```agda
coherence-source-target-globular-diagram :
  {l : Level} {A : ℕ → UU l}
  (s : (n : ℕ) → A (succ-ℕ n) → A n)
  (t : (n : ℕ) → A (succ-ℕ n) → A n) → UU l
coherence-source-target-globular-diagram s t =
  ( (n : ℕ) → s n ∘ s (succ-ℕ n) ~ s n ∘ t (succ-ℕ n)) ×
  ( (n : ℕ) → t n ∘ s (succ-ℕ n) ~ t n ∘ t (succ-ℕ n))

globular-diagram : (l : Level) → UU (lsuc l)
globular-diagram l =
  Σ ( ℕ → UU l)
    ( λ A →
      Σ ( (n : ℕ) → (A (succ-ℕ n) → A n))
        ( λ s →
          Σ ( (n : ℕ) → (A (succ-ℕ n) → A n))
            ( λ t → coherence-source-target-globular-diagram s t)))

module _
  {l : Level} (A : globular-diagram l)
  where

  family-globular-diagram : ℕ → UU l
  family-globular-diagram = pr1 A

  source-map-globular-diagram :
    (n : ℕ) → family-globular-diagram (succ-ℕ n) → family-globular-diagram n
  source-map-globular-diagram = pr1 (pr2 A)

  target-map-globular-diagram :
    (n : ℕ) → family-globular-diagram (succ-ℕ n) → family-globular-diagram n
  target-map-globular-diagram = pr1 (pr2 (pr2 A))

  coh-globular-diagram :
    coherence-source-target-globular-diagram
      ( source-map-globular-diagram)
      ( target-map-globular-diagram)
  coh-globular-diagram = pr2 (pr2 (pr2 A))

  coh-source-globular-diagram :
    (n : ℕ) →
    source-map-globular-diagram n ∘ source-map-globular-diagram (succ-ℕ n) ~
    source-map-globular-diagram n ∘ target-map-globular-diagram (succ-ℕ n)
  coh-source-globular-diagram = pr1 coh-globular-diagram

  coh-target-globular-diagram :
    (n : ℕ) →
    target-map-globular-diagram n ∘ source-map-globular-diagram (succ-ℕ n) ~
    target-map-globular-diagram n ∘ target-map-globular-diagram (succ-ℕ n)
  coh-target-globular-diagram = pr2 coh-globular-diagram
```

## Operations

### Right shifting a globular diagram

We can **right shift** a globular diagram of types by forgetting the first
terms.

```agda
right-shift-globular-diagram :
  {l : Level} → globular-diagram l → globular-diagram l
right-shift-globular-diagram A =
  ( family-globular-diagram A ∘ succ-ℕ ,
    source-map-globular-diagram A ∘ succ-ℕ ,
    target-map-globular-diagram A ∘ succ-ℕ ,
    coh-source-globular-diagram A ∘ succ-ℕ ,
    coh-target-globular-diagram A ∘ succ-ℕ)

iterated-right-shift-globular-diagram :
  {l : Level} → ℕ → globular-diagram l → globular-diagram l
iterated-right-shift-globular-diagram n =
  iterate n right-shift-globular-diagram
```

### Left shifting a globular diagram

We can **left shift** a globular diagram of types by padding it with the
[terminal type](foundation.unit-type.md) `unit`.

```agda
left-shift-globular-diagram :
  {l : Level} → globular-diagram l → globular-diagram l
pr1 (left-shift-globular-diagram {l} A) zero-ℕ =
  raise-unit l
pr1 (left-shift-globular-diagram A) (succ-ℕ n) =
  family-globular-diagram A n
pr1 (pr2 (left-shift-globular-diagram A)) zero-ℕ =
  raise-terminal-map (family-globular-diagram A 0)
pr1 (pr2 (left-shift-globular-diagram A)) (succ-ℕ n) =
  source-map-globular-diagram A n
pr1 (pr2 (pr2 (left-shift-globular-diagram A))) zero-ℕ =
  raise-terminal-map (family-globular-diagram A 0)
pr1 (pr2 (pr2 (left-shift-globular-diagram A))) (succ-ℕ n) =
  target-map-globular-diagram A n
pr1 (pr2 (pr2 (pr2 (left-shift-globular-diagram A)))) zero-ℕ =
  refl-htpy
pr1 (pr2 (pr2 (pr2 (left-shift-globular-diagram A)))) (succ-ℕ n) =
  coh-source-globular-diagram A n
pr2 (pr2 (pr2 (pr2 (left-shift-globular-diagram A)))) zero-ℕ =
  refl-htpy
pr2 (pr2 (pr2 (pr2 (left-shift-globular-diagram A)))) (succ-ℕ n) =
  coh-target-globular-diagram A n

iterated-left-shift-globular-diagram :
  {l : Level} (n : ℕ) →
  globular-diagram l → globular-diagram l
iterated-left-shift-globular-diagram n =
  iterate n left-shift-globular-diagram
```

### Postcomposition globular diagrams

Given a globular diagram `A` and a type `X` there is a globular diagram `X → A`
defined by levelwise postcomposition

```text
    (s₃ ∘ -)          (s₂ ∘ -)          (s₁ ∘ -)          (s₀ ∘ -)
    ------->          ------->          ------->          ------->
  ⋯          (X → A₃)          (X → A₂)          (X → A₁)          (X → A₀).
    ------->          ------->          ------->          ------->
    (t₃ ∘ -)          (t₂ ∘ -)          (t₁ ∘ -)          (t₀ ∘ -)
```

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : globular-diagram l2)
  where

  postcomp-globular-diagram : globular-diagram (l1 ⊔ l2)
  postcomp-globular-diagram =
    ( λ n → X → family-globular-diagram A n) ,
    ( λ n → postcomp X (source-map-globular-diagram A n)) ,
    ( λ n → postcomp X (target-map-globular-diagram A n)) ,
    ( λ n → htpy-postcomp X (coh-source-globular-diagram A n)) ,
    ( λ n → htpy-postcomp X (coh-target-globular-diagram A n))
```

## See also

- [Globular types](structured-types.globular-types.md)
