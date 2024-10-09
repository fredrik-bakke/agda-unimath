# Dependent globular diagrams of types

```agda
module structured-types.dependent-globular-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.constant-type-families
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-inverse-sequential-diagrams
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterating-dependent-functions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies

open import structured-types.globular-diagrams
```

</details>

## Idea

A **dependent globular diagram** `B` over a base
[globular diagram](foundation.globular-diagrams.md) `A` is a
[sequence](foundation.sequences.md) of families over each `Aₙ` together with a
pair of source/target families of maps

```text
  σₙ : (x : Aₙ₊₁) → Bₙ₊₁(x) → Bₙ(sₙ(x)), and
  τₙ : (x : Aₙ₊₁) → Bₙ₊₁(x) → Bₙ(tₙ(x))
```

where `s` and `t` are the source and target maps of the base globular diagram,
such that the dependent diagrams

```text
                 Bₙ₊₂(x)
         σₙ₊₁  /         \ τₙ₊₁
              /           \
             /             \
    Bₙ₊₁(sₙ₊₁(x))         Bₙ₊₁(tₙ₊₁(x))
             \             /
          σₙ  \           / σₙ
               \         /
  Bₙ₊₁(sₙ(sₙ₊₁(x))) === Bₙ₊₁(sₙ(tₙ₊₁(x)))
```

and

```text
                 Bₙ₊₂(x)
         σₙ₊₁  /         \ τₙ₊₁
              /           \
             /             \
    Bₙ₊₁(sₙ₊₁(x))         Bₙ₊₁(tₙ₊₁(x))
             \             /
           τₙ \           / τₙ
               \         /
  Bₙ₊₁(tₙ(sₙ₊₁(x))) === Bₙ₊₁(tₙ(tₙ₊₁(x)))
```

commute.

## Definitions

### The coherence laws of dependent globular diagrams of types

```agda
module _
  {l1 l2 : Level} (A : globular-diagram l1)
  (B : (n : ℕ) → family-globular-diagram A n → UU l2)
  (σ :
    (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
    B (succ-ℕ n) x → B n (source-map-globular-diagram A n x))
  (τ :
    (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
    B (succ-ℕ n) x → B n (target-map-globular-diagram A n x))
  where

  coherence-source-dependent-globular-diagram : UU (l1 ⊔ l2)
  coherence-source-dependent-globular-diagram =
    (n : ℕ)
    (x : family-globular-diagram A (succ-ℕ (succ-ℕ n)))
    (y : B (succ-ℕ (succ-ℕ n)) x) →
    dependent-identification
      ( B n)
      ( coh-source-globular-diagram A n x)
      ( σ n (source-map-globular-diagram A (succ-ℕ n) x) (σ (succ-ℕ n) x y))
      ( σ n (target-map-globular-diagram A (succ-ℕ n) x) (τ (succ-ℕ n) x y))

  coherence-target-dependent-globular-diagram : UU (l1 ⊔ l2)
  coherence-target-dependent-globular-diagram =
    (n : ℕ)
    (x : family-globular-diagram A (succ-ℕ (succ-ℕ n)))
    (y : B (succ-ℕ (succ-ℕ n)) x) →
    dependent-identification
      ( B n)
      ( coh-target-globular-diagram A n x)
      ( τ n (source-map-globular-diagram A (succ-ℕ n) x) (σ (succ-ℕ n) x y))
      ( τ n (target-map-globular-diagram A (succ-ℕ n) x) (τ (succ-ℕ n) x y))

  coherence-dependent-globular-diagram : UU (l1 ⊔ l2)
  coherence-dependent-globular-diagram =
    coherence-source-dependent-globular-diagram ×
    coherence-target-dependent-globular-diagram

  coherence-source-coherence-dependent-globular-diagram :
    coherence-dependent-globular-diagram →
    coherence-source-dependent-globular-diagram
  coherence-source-coherence-dependent-globular-diagram = pr1

  coherence-target-coherence-dependent-globular-diagram :
    coherence-dependent-globular-diagram →
    coherence-target-dependent-globular-diagram
  coherence-target-coherence-dependent-globular-diagram = pr2
```

### Dependent globular diagrams of types

```agda
dependent-globular-diagram :
  {l1 : Level} (l2 : Level) (A : globular-diagram l1) →
  UU (l1 ⊔ lsuc l2)
dependent-globular-diagram l2 A =
  Σ ( (n : ℕ) → family-globular-diagram A n → UU l2)
    ( λ B →
      Σ ( (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
          B (succ-ℕ n) x → B n (source-map-globular-diagram A n x))
        ( λ σ →
          Σ ( (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
              B (succ-ℕ n) x → B n (target-map-globular-diagram A n x))
            ( λ τ → coherence-dependent-globular-diagram A B σ τ)))

module _
  {l1 l2 : Level} (A : globular-diagram l1)
  (B : dependent-globular-diagram l2 A)
  where

  family-dependent-globular-diagram :
    (n : ℕ) → family-globular-diagram A n → UU l2
  family-dependent-globular-diagram = pr1 B

  source-map-dependent-globular-diagram :
    (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
    family-dependent-globular-diagram (succ-ℕ n) x →
    family-dependent-globular-diagram n (source-map-globular-diagram A n x)
  source-map-dependent-globular-diagram = pr1 (pr2 B)

  target-map-dependent-globular-diagram :
    (n : ℕ) (x : family-globular-diagram A (succ-ℕ n)) →
    family-dependent-globular-diagram (succ-ℕ n) x →
    family-dependent-globular-diagram n (target-map-globular-diagram A n x)
  target-map-dependent-globular-diagram = pr1 (pr2 (pr2 B))

  coh-dependent-globular-diagram :
    coherence-dependent-globular-diagram A
      family-dependent-globular-diagram
      source-map-dependent-globular-diagram
      target-map-dependent-globular-diagram
  coh-dependent-globular-diagram = pr2 (pr2 (pr2 B))

  coh-source-dependent-globular-diagram :
    coherence-source-dependent-globular-diagram A
      family-dependent-globular-diagram
      source-map-dependent-globular-diagram
      target-map-dependent-globular-diagram
  coh-source-dependent-globular-diagram =
    coherence-source-coherence-dependent-globular-diagram A
      family-dependent-globular-diagram
      source-map-dependent-globular-diagram
      target-map-dependent-globular-diagram
      coh-dependent-globular-diagram

  coh-target-dependent-globular-diagram :
    coherence-target-dependent-globular-diagram A
      family-dependent-globular-diagram
      source-map-dependent-globular-diagram
      target-map-dependent-globular-diagram
  coh-target-dependent-globular-diagram =
    coherence-target-coherence-dependent-globular-diagram A
      family-dependent-globular-diagram
      source-map-dependent-globular-diagram
      target-map-dependent-globular-diagram
      coh-dependent-globular-diagram
```

### The source and target dependent inverse sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : globular-diagram l1) (B : dependent-globular-diagram l2 A)
  where

  source-dependent-inverse-sequential-diagram-dependent-globular-diagram :
    dependent-inverse-sequential-diagram l2
      ( source-inverse-sequential-diagram-globular-diagram A)
  source-dependent-inverse-sequential-diagram-dependent-globular-diagram =
    ( family-dependent-globular-diagram A B ,
      source-map-dependent-globular-diagram A B)

  target-dependent-inverse-sequential-diagram-dependent-globular-diagram :
    dependent-inverse-sequential-diagram l2
      ( target-inverse-sequential-diagram-globular-diagram A)
  target-dependent-inverse-sequential-diagram-dependent-globular-diagram =
    ( family-dependent-globular-diagram A B ,
      target-map-dependent-globular-diagram A B)
```

### Constant dependent globular diagrams of types

```agda
module _
  {l1 l2 : Level}
  (A : globular-diagram l1) (B : globular-diagram l2)
  where

  coh-source-const-dependent-globular-diagram :
    coherence-source-dependent-globular-diagram A
      ( λ n _ → family-globular-diagram B n)
      ( λ n _ → source-map-globular-diagram B n)
      ( λ n _ → target-map-globular-diagram B n)
  coh-source-const-dependent-globular-diagram n x =
    ( ( tr-constant-type-family (coh-source-globular-diagram A n x)) ·r
      ( source-map-globular-diagram B n ∘
        source-map-globular-diagram B (succ-ℕ n))) ∙h
    ( coh-source-globular-diagram B n)

  coh-target-const-dependent-globular-diagram :
    coherence-target-dependent-globular-diagram A
      ( λ n _ → family-globular-diagram B n)
      ( λ n _ → source-map-globular-diagram B n)
      ( λ n _ → target-map-globular-diagram B n)
  coh-target-const-dependent-globular-diagram n x =
    ( ( tr-constant-type-family (coh-target-globular-diagram A n x)) ·r
      ( target-map-globular-diagram B n ∘
        source-map-globular-diagram B (succ-ℕ n))) ∙h
    ( coh-target-globular-diagram B n)

  coh-const-dependent-globular-diagram :
    coherence-dependent-globular-diagram A
      ( λ n _ → family-globular-diagram B n)
      ( λ n _ → source-map-globular-diagram B n)
      ( λ n _ → target-map-globular-diagram B n)
  coh-const-dependent-globular-diagram =
    coh-source-const-dependent-globular-diagram ,
    coh-target-const-dependent-globular-diagram

  const-dependent-globular-diagram :
    dependent-globular-diagram l2 A
  const-dependent-globular-diagram =
    ( λ n _ → family-globular-diagram B n) ,
    ( λ n _ → source-map-globular-diagram B n) ,
    ( λ n _ → target-map-globular-diagram B n) ,
    ( coh-const-dependent-globular-diagram)
```

### Sections of a dependent globular diagram

A **section** of a dependent globular diagram `B` over `A` is a choice of
sections `hₙ` of each `Bₙ` that vary naturally over `A`, by which we mean that
the diagrams

```text
            σₙ                        τₙ
      Bₙ₊₁ ----> Bₙ              Bₙ₊₁ ----> Bₙ
      ∧          ∧              ∧          ∧
  hₙ₊₁|          | hₙ        hₙ₊₁|          | hₙ
      |          |              |          |
      Aₙ₊₁ ----> Aₙ              Aₙ₊₁ ----> Aₙ
            sₙ                        tₙ
```

commute for each `n : ℕ`.

```agda
module _
  {l1 l2 : Level} (A : globular-diagram l1)
  (B : dependent-globular-diagram l2 A)
  where

  naturality-source-section-dependent-globular-diagram :
    ( (n : ℕ) (x : family-globular-diagram A n) →
      family-dependent-globular-diagram A B n x) → UU (l1 ⊔ l2)
  naturality-source-section-dependent-globular-diagram h =
    (n : ℕ) →
    naturality-section-dependent-inverse-sequential-diagram
      ( source-inverse-sequential-diagram-globular-diagram A)
      ( source-dependent-inverse-sequential-diagram-dependent-globular-diagram
        ( A)
        ( B))
      ( h)
      ( n)

  naturality-target-section-dependent-globular-diagram :
    ( (n : ℕ) (x : family-globular-diagram A n) →
      family-dependent-globular-diagram A B n x) → UU (l1 ⊔ l2)
  naturality-target-section-dependent-globular-diagram h =
    (n : ℕ) →
    naturality-section-dependent-inverse-sequential-diagram
      ( target-inverse-sequential-diagram-globular-diagram A)
      ( target-dependent-inverse-sequential-diagram-dependent-globular-diagram
        ( A)
        ( B))
      ( h)
      ( n)

  naturality-section-dependent-globular-diagram :
    ( (n : ℕ) (x : family-globular-diagram A n) →
      family-dependent-globular-diagram A B n x) →
    UU (l1 ⊔ l2)
  naturality-section-dependent-globular-diagram h =
    ( naturality-source-section-dependent-globular-diagram h) ×
    ( naturality-target-section-dependent-globular-diagram h)

  section-dependent-globular-diagram : UU (l1 ⊔ l2)
  section-dependent-globular-diagram =
    Σ ( (n : ℕ) (x : family-globular-diagram A n) →
        family-dependent-globular-diagram A B n x)
      ( λ h → naturality-section-dependent-globular-diagram h)

  map-section-dependent-globular-diagram :
    section-dependent-globular-diagram →
    (n : ℕ) (x : family-globular-diagram A n) →
    family-dependent-globular-diagram A B n x
  map-section-dependent-globular-diagram = pr1

  naturality-map-section-dependent-globular-diagram :
    (f : section-dependent-globular-diagram) →
    naturality-section-dependent-globular-diagram
      ( map-section-dependent-globular-diagram f)
  naturality-map-section-dependent-globular-diagram = pr2

  naturality-source-map-section-dependent-globular-diagram :
    (f : section-dependent-globular-diagram) →
    naturality-source-section-dependent-globular-diagram
      ( map-section-dependent-globular-diagram f)
  naturality-source-map-section-dependent-globular-diagram f =
    pr1 (naturality-map-section-dependent-globular-diagram f)

  naturality-target-map-section-dependent-globular-diagram :
    (f : section-dependent-globular-diagram) →
    naturality-target-section-dependent-globular-diagram
      ( map-section-dependent-globular-diagram f)
  naturality-target-map-section-dependent-globular-diagram f =
    pr2 (naturality-map-section-dependent-globular-diagram f)
```

## Operations

### Right shifting a dependent globular diagram

We can **right shift** a dependent globular diagram of types by forgetting the
first terms.

```agda
right-shift-dependent-globular-diagram :
  {l1 l2 : Level} (A : globular-diagram l1) →
  dependent-globular-diagram l2 A →
  dependent-globular-diagram l2 (right-shift-globular-diagram A)
right-shift-dependent-globular-diagram A B =
  ( family-dependent-globular-diagram A B ∘ succ-ℕ ,
    source-map-dependent-globular-diagram A B ∘ succ-ℕ ,
    target-map-dependent-globular-diagram A B ∘ succ-ℕ ,
    coh-source-dependent-globular-diagram A B ∘ succ-ℕ ,
    coh-target-dependent-globular-diagram A B ∘ succ-ℕ)

iterated-right-shift-dependent-globular-diagram :
  {l1 l2 : Level} (n : ℕ) →
  (A : globular-diagram l1) →
  dependent-globular-diagram l2 A →
  dependent-globular-diagram l2 (iterated-right-shift-globular-diagram n A)
iterated-right-shift-dependent-globular-diagram n A B =
  iterate-dependent n right-shift-dependent-globular-diagram A B
```

### Left shifting a dependent globular diagram

We can **left shift** a dependent globular diagram of types by padding it with
the [terminal type](foundation.unit-type.md) `unit`.

```agda
module _
  {l1 l2 : Level} (A : globular-diagram l1)
  (B : dependent-globular-diagram l2 A)
  where

  family-left-shift-dependent-globular-diagram :
    (n : ℕ) → family-left-shift-globular-diagram A n → UU l2
  family-left-shift-dependent-globular-diagram zero-ℕ _ =
    raise-unit l2
  family-left-shift-dependent-globular-diagram (succ-ℕ n) =
    family-dependent-globular-diagram A B n

  source-map-left-shift-dependent-globular-diagram :
    (n : ℕ) (x : family-left-shift-globular-diagram A (succ-ℕ n)) →
    family-left-shift-dependent-globular-diagram
      ( succ-ℕ n)
      ( x) →
    family-left-shift-dependent-globular-diagram
      ( n)
      ( source-map-left-shift-globular-diagram A n x)
  source-map-left-shift-dependent-globular-diagram zero-ℕ x =
    raise-terminal-map (family-dependent-globular-diagram A B 0 x)
  source-map-left-shift-dependent-globular-diagram (succ-ℕ n) =
    source-map-dependent-globular-diagram A B n

  target-map-left-shift-dependent-globular-diagram :
    (n : ℕ) (x : family-left-shift-globular-diagram A (succ-ℕ n)) →
    family-left-shift-dependent-globular-diagram
      ( succ-ℕ n)
      ( x) →
    family-left-shift-dependent-globular-diagram
      ( n)
      ( target-map-left-shift-globular-diagram A n x)
  target-map-left-shift-dependent-globular-diagram zero-ℕ x =
    raise-terminal-map (family-dependent-globular-diagram A B 0 x)
  target-map-left-shift-dependent-globular-diagram (succ-ℕ n) =
    target-map-dependent-globular-diagram A B n

  coh-source-left-shift-dependent-globular-diagram :
    coherence-source-dependent-globular-diagram
      ( left-shift-globular-diagram A)
      ( family-left-shift-dependent-globular-diagram)
      ( source-map-left-shift-dependent-globular-diagram)
      ( target-map-left-shift-dependent-globular-diagram)
  coh-source-left-shift-dependent-globular-diagram zero-ℕ x y = refl
  coh-source-left-shift-dependent-globular-diagram (succ-ℕ n) =
    coh-source-dependent-globular-diagram A B n

  coh-target-left-shift-dependent-globular-diagram :
    coherence-target-dependent-globular-diagram
      ( left-shift-globular-diagram A)
      ( family-left-shift-dependent-globular-diagram)
      ( source-map-left-shift-dependent-globular-diagram)
      ( target-map-left-shift-dependent-globular-diagram)
  coh-target-left-shift-dependent-globular-diagram zero-ℕ x y = refl
  coh-target-left-shift-dependent-globular-diagram (succ-ℕ n) =
    coh-target-dependent-globular-diagram A B n

  coh-left-shift-dependent-globular-diagram :
    coherence-dependent-globular-diagram
      ( left-shift-globular-diagram A)
      ( family-left-shift-dependent-globular-diagram)
      ( source-map-left-shift-dependent-globular-diagram)
      ( target-map-left-shift-dependent-globular-diagram)
  coh-left-shift-dependent-globular-diagram =
    coh-source-left-shift-dependent-globular-diagram ,
    coh-target-left-shift-dependent-globular-diagram

  left-shift-dependent-globular-diagram :
    dependent-globular-diagram l2 (left-shift-globular-diagram A)
  left-shift-dependent-globular-diagram =
    family-left-shift-dependent-globular-diagram ,
    source-map-left-shift-dependent-globular-diagram ,
    target-map-left-shift-dependent-globular-diagram ,
    coh-left-shift-dependent-globular-diagram

iterated-left-shift-dependent-globular-diagram :
  {l1 l2 : Level} (n : ℕ) →
  (A : globular-diagram l1) →
  dependent-globular-diagram l2 A →
  dependent-globular-diagram l2 (iterated-left-shift-globular-diagram n A)
iterated-left-shift-dependent-globular-diagram n A B =
  iterate-dependent n left-shift-dependent-globular-diagram A B
```
