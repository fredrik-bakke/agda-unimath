# Finite Σ-decompositions of finite types

```agda
module univalent-combinatorics.sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.sigma-decompositions public

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

## Definition

```agda
Σ-Decomposition-𝔽 :
  {l : Level} → (l1 l2 : Level) → 𝔽 l → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
Σ-Decomposition-𝔽 l1 l2 A =
  Σ ( 𝔽 l1)
    ( λ X →
      Σ ( type-𝔽 X → Inhabited-Type-𝔽 l2)
        ( λ Y → equiv-𝔽 A (Σ-𝔽 X (λ x → finite-type-Inhabited-Type-𝔽 (Y x)))))

module _
  {l l1 l2 : Level} (A : 𝔽 l) (D : Σ-Decomposition-𝔽 l1 l2 A)
  where

  finite-indexing-type-Σ-Decomposition-𝔽 : 𝔽 l1
  finite-indexing-type-Σ-Decomposition-𝔽 = pr1 D

  indexing-type-Σ-Decomposition-𝔽 : UU l1
  indexing-type-Σ-Decomposition-𝔽 =
    type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽

  is-finite-indexing-type-Σ-Decomposition-𝔽 :
    is-finite (indexing-type-Σ-Decomposition-𝔽)
  is-finite-indexing-type-Σ-Decomposition-𝔽 =
    is-finite-type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽

  finite-inhabited-cotype-Σ-Decomposition-𝔽 :
    Fam-Inhabited-Types-𝔽 l2 finite-indexing-type-Σ-Decomposition-𝔽
  finite-inhabited-cotype-Σ-Decomposition-𝔽 = pr1 (pr2 D)

  finite-cotype-Σ-Decomposition-𝔽 :
    type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽 → 𝔽 l2
  finite-cotype-Σ-Decomposition-𝔽 =
    finite-type-Fam-Inhabited-Types-𝔽
      finite-indexing-type-Σ-Decomposition-𝔽
      finite-inhabited-cotype-Σ-Decomposition-𝔽

  cotype-Σ-Decomposition-𝔽 :
    type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽 → UU l2
  cotype-Σ-Decomposition-𝔽 x = type-𝔽 (finite-cotype-Σ-Decomposition-𝔽 x)

  is-inhabited-cotype-Σ-Decomposition-𝔽 :
   (x : type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽) →
    is-inhabited (cotype-Σ-Decomposition-𝔽 x)
  is-inhabited-cotype-Σ-Decomposition-𝔽 x =
    is-inhabited-type-Inhabited-Type-𝔽
      ( finite-inhabited-cotype-Σ-Decomposition-𝔽 x)

  inhabited-cotype-Σ-Decomposition-𝔽 :
    Fam-Inhabited-Types l2 indexing-type-Σ-Decomposition-𝔽
  pr1 (inhabited-cotype-Σ-Decomposition-𝔽 x) =
    cotype-Σ-Decomposition-𝔽 x
  pr2 (inhabited-cotype-Σ-Decomposition-𝔽 x) =
    is-inhabited-cotype-Σ-Decomposition-𝔽 x

  matching-correspondence-Σ-Decomposition-𝔽 :
    type-𝔽 A ≃ Σ indexing-type-Σ-Decomposition-𝔽 cotype-Σ-Decomposition-𝔽
  matching-correspondence-Σ-Decomposition-𝔽 = pr2 (pr2 D)

  map-matching-correspondence-Σ-Decomposition-𝔽 :
    type-𝔽 A → Σ indexing-type-Σ-Decomposition-𝔽 cotype-Σ-Decomposition-𝔽
  map-matching-correspondence-Σ-Decomposition-𝔽 =
    map-equiv matching-correspondence-Σ-Decomposition-𝔽

  Σ-Decomposition-Σ-Decomposition-𝔽 :
    Σ-Decomposition l1 l2 (type-𝔽 A)
  pr1 Σ-Decomposition-Σ-Decomposition-𝔽 =
    indexing-type-Σ-Decomposition-𝔽
  pr1 (pr2 Σ-Decomposition-Σ-Decomposition-𝔽) =
    inhabited-cotype-Σ-Decomposition-𝔽
  pr2 (pr2 Σ-Decomposition-Σ-Decomposition-𝔽) =
    matching-correspondence-Σ-Decomposition-𝔽
```

### Fibered double finite Σ-Decompositions

```agda
fibered-Σ-Decomposition-𝔽 :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : 𝔽 l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
fibered-Σ-Decomposition-𝔽 l2 l3 l4 l5 A =
  Σ (Σ-Decomposition-𝔽 l2 l3 A)
    (λ D → Σ-Decomposition-𝔽 l4 l5 (finite-indexing-type-Σ-Decomposition-𝔽 A D))
```

### Displayed double Σ-decompositions

```agda
displayed-Σ-Decomposition-𝔽 :
  {l1 : Level} (l2 l3 l4 l5 : Level) (A : 𝔽 l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
displayed-Σ-Decomposition-𝔽 l2 l3 l4 l5 A =
  ( Σ (Σ-Decomposition-𝔽 l2 l3 A)
  (λ D → (u : indexing-type-Σ-Decomposition-𝔽 A D) →
  Σ-Decomposition-𝔽 l4 l5 (finite-cotype-Σ-Decomposition-𝔽 A D u)))
```

## Properties

### Characterization of the equality of finite Σ-Decompositions

```agda
module _
   {l1 l2 l3 : Level} (A : 𝔽 l1)
  where

  is-finite-Σ-Decomposition :
    subtype (l2 ⊔ l3) (Σ-Decomposition l2 l3 (type-𝔽 A))
  is-finite-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Prop (indexing-type-Σ-Decomposition D))
      ( λ _ →
        Π-Prop
          ( indexing-type-Σ-Decomposition D)
          ( λ x → is-finite-Prop (cotype-Σ-Decomposition D x)))

  map-Σ-Decomposition-𝔽-subtype-is-finite :
    type-subtype is-finite-Σ-Decomposition → Σ-Decomposition-𝔽 l2 l3 A
  map-Σ-Decomposition-𝔽-subtype-is-finite ((X , (Y , e)) , (fin-X , fin-Y)) =
    ( ( X , fin-X ) ,
        ( ( λ x →
            ( (type-Inhabited-Type (Y x)) , (fin-Y x)) ,
              (is-inhabited-type-Inhabited-Type (Y x))) ,
        e ))

  map-inv-Σ-Decomposition-𝔽-subtype-is-finite :
    Σ-Decomposition-𝔽 l2 l3 A → type-subtype is-finite-Σ-Decomposition
  map-inv-Σ-Decomposition-𝔽-subtype-is-finite ((X , fin-X) , (Y , e)) =
    ( ( X ,
        ( ( λ x → inhabited-type-Inhabited-Type-𝔽 (Y x) ) ,
          ( e))) ,
      (fin-X , (λ x → is-finite-Inhabited-Type-𝔽 (Y x))))

  equiv-Σ-Decomposition-𝔽-is-finite-subtype :
    type-subtype is-finite-Σ-Decomposition ≃ Σ-Decomposition-𝔽 l2 l3 A
  pr1 (equiv-Σ-Decomposition-𝔽-is-finite-subtype) =
    map-Σ-Decomposition-𝔽-subtype-is-finite
  pr2 (equiv-Σ-Decomposition-𝔽-is-finite-subtype) =
    is-equiv-has-inverse
      map-inv-Σ-Decomposition-𝔽-subtype-is-finite
      refl-htpy
      refl-htpy

  is-emb-Σ-Decomposition-Σ-Decomposition-𝔽 :
    is-emb (Σ-Decomposition-Σ-Decomposition-𝔽 {l1} {l2} {l3} A )
  is-emb-Σ-Decomposition-Σ-Decomposition-𝔽 =
    is-emb-triangle-is-equiv
      ( Σ-Decomposition-Σ-Decomposition-𝔽 A)
      ( pr1)
      ( map-inv-equiv ( equiv-Σ-Decomposition-𝔽-is-finite-subtype))
      ( refl-htpy)
      ( is-equiv-map-inv-equiv
        ( equiv-Σ-Decomposition-𝔽-is-finite-subtype))
      ( is-emb-inclusion-subtype (is-finite-Σ-Decomposition))

  emb-Σ-Decomposition-Σ-Decomposition-𝔽 :
    Σ-Decomposition-𝔽 l2 l3 A ↪ Σ-Decomposition l2 l3 (type-𝔽 A)
  pr1 (emb-Σ-Decomposition-Σ-Decomposition-𝔽) =
    Σ-Decomposition-Σ-Decomposition-𝔽 A
  pr2 (emb-Σ-Decomposition-Σ-Decomposition-𝔽) =
    is-emb-Σ-Decomposition-Σ-Decomposition-𝔽

module _
  {l1 l2 l3 : Level} {A : 𝔽 l1}
  (X : Σ-Decomposition-𝔽 l2 l3 A) (Y : Σ-Decomposition-𝔽 l2 l3 A)
  where

  equiv-Σ-Decomposition-𝔽 :
    UU (l1 ⊔ l2 ⊔ l3 )
  equiv-Σ-Decomposition-𝔽 =
    equiv-Σ-Decomposition
      ( Σ-Decomposition-Σ-Decomposition-𝔽 A X)
      ( Σ-Decomposition-Σ-Decomposition-𝔽 A Y)

  extensionality-Σ-Decomposition-𝔽 :
    (X ＝ Y) ≃ equiv-Σ-Decomposition-𝔽
  extensionality-Σ-Decomposition-𝔽 =
     extensionality-Σ-Decomposition
       ( Σ-Decomposition-Σ-Decomposition-𝔽 A X)
       ( Σ-Decomposition-Σ-Decomposition-𝔽 A Y) ∘e
     equiv-ap-emb (emb-Σ-Decomposition-Σ-Decomposition-𝔽 A)
```

### Iterated finite Σ-Decomposition

#### Fibered finite Σ-Decomposition as a subtype

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (A : 𝔽 l1)
  where

  is-finite-fibered-Σ-Decomposition :
    subtype (l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( fibered-Σ-Decomposition l2 l3 l4 l5 (type-𝔽 A))
  is-finite-fibered-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Σ-Decomposition A (fst-fibered-Σ-Decomposition D))
      ( λ p →
        is-finite-Σ-Decomposition
          ( (indexing-type-fst-fibered-Σ-Decomposition D) , (pr1 p))
          ( snd-fibered-Σ-Decomposition D) )

  equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtype :
    type-subtype is-finite-fibered-Σ-Decomposition ≃
    fibered-Σ-Decomposition-𝔽 l2 l3 l4 l5 A
  equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtype =
     equiv-Σ
       ( λ D →
         Σ-Decomposition-𝔽 l4 l5 ( finite-indexing-type-Σ-Decomposition-𝔽 A D))
       ( equiv-Σ-Decomposition-𝔽-is-finite-subtype A)
       ( λ x →
         equiv-Σ-Decomposition-𝔽-is-finite-subtype
           ( ( indexing-type-Σ-Decomposition (pr1 x)) ,
             (pr1 (pr2 x)))) ∘e
       interchange-Σ-Σ
         ( λ D D' p →
           type-Prop
             ( is-finite-Σ-Decomposition
               ( indexing-type-Σ-Decomposition D , pr1 p)
               D'))
```

#### Displayed finite Σ-Decomposition as a subtype

```agda
  is-finite-displayed-Σ-Decomposition :
    subtype (l2 ⊔ l3 ⊔ l4 ⊔ l5)
      ( displayed-Σ-Decomposition l2 l3 l4 l5 (type-𝔽 A))
  is-finite-displayed-Σ-Decomposition D =
    Σ-Prop
      ( is-finite-Σ-Decomposition A (fst-displayed-Σ-Decomposition D))
      ( λ p →
        Π-Prop
          ( indexing-type-fst-displayed-Σ-Decomposition D)
          ( λ x →
            is-finite-Σ-Decomposition
              ( ( cotype-fst-displayed-Σ-Decomposition D x) , (pr2 p x))
              ( snd-displayed-Σ-Decomposition D x) ))

  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtype :
    type-subtype is-finite-displayed-Σ-Decomposition ≃
    displayed-Σ-Decomposition-𝔽 l2 l3 l4 l5 A
  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtype =
     equiv-Σ
       ( λ D →
         ( x : indexing-type-Σ-Decomposition-𝔽 A D) →
         ( Σ-Decomposition-𝔽 l4 l5 ( finite-cotype-Σ-Decomposition-𝔽 A D x)))
       ( equiv-Σ-Decomposition-𝔽-is-finite-subtype A)
       ( λ D1 →
         equiv-Π
           ( λ z →
             Σ-Decomposition-𝔽 l4 l5
               ( finite-cotype-Σ-Decomposition-𝔽 A
                 ( map-equiv
                   ( equiv-Σ-Decomposition-𝔽-is-finite-subtype A) D1) z))
           ( id-equiv)
           ( λ x →
             equiv-Σ-Decomposition-𝔽-is-finite-subtype
               (finite-cotype-Σ-Decomposition-𝔽 A
                 ( map-equiv
                   ( equiv-Σ-Decomposition-𝔽-is-finite-subtype A) D1) x)) ∘e
           inv-distributive-Π-Σ ) ∘e
       interchange-Σ-Σ _
```

#### Fibered finite Σ-decompositions and displayed finite Σ-Decomposition are equivalent

```agda
module _
  {l1 l : Level} (A : 𝔽 l1)
  (D : fibered-Σ-Decomposition l l l l (type-𝔽 A))
  where

  map-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-fibered-Σ-Decomposition A D) →
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D))
  pr1 (pr1 (map-is-finite-displayed-fibered-Σ-Decomposition p)) =
    pr1 (pr2 p)
  pr2 (pr1 (map-is-finite-displayed-fibered-Σ-Decomposition p)) =
    λ u → is-finite-Σ (pr2 (pr2 p) u) (λ v → (pr2 (pr1 p)) _ )
  pr1 (pr2 (map-is-finite-displayed-fibered-Σ-Decomposition p) u) =
    pr2 (pr2 p) u
  pr2 (pr2 (map-is-finite-displayed-fibered-Σ-Decomposition p) u) =
    λ v → (pr2 (pr1 p)) _

  map-inv-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D)) →
    type-Prop (is-finite-fibered-Σ-Decomposition A D)
  pr1 (pr1 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    is-finite-equiv
      ( inv-equiv (matching-correspondence-snd-fibered-Σ-Decomposition D))
      ( is-finite-Σ (pr1 (pr1 p)) λ u → (pr1 (pr2 p u)))
  pr2 (pr1 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    map-inv-equiv
      ( equiv-precomp-Π
        ( inv-equiv ( matching-correspondence-snd-fibered-Σ-Decomposition D))
        ( λ z → is-finite (cotype-fst-fibered-Σ-Decomposition D z)))
      λ uv → pr2 (pr2 p (pr1 uv)) (pr2 uv)
  pr1 (pr2 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    pr1 (pr1 p)
  pr2 (pr2 (map-inv-is-finite-displayed-fibered-Σ-Decomposition p)) =
    λ u → pr1 (pr2 p u)

  equiv-is-finite-displayed-fibered-Σ-Decomposition :
    type-Prop (is-finite-fibered-Σ-Decomposition A D) ≃
    type-Prop (is-finite-displayed-Σ-Decomposition A
      (map-equiv equiv-displayed-fibered-Σ-Decomposition D))
  equiv-is-finite-displayed-fibered-Σ-Decomposition =
    equiv-prop
      ( is-prop-type-Prop (is-finite-fibered-Σ-Decomposition A D))
      ( is-prop-type-Prop
        ( is-finite-displayed-Σ-Decomposition A
          ( map-equiv equiv-displayed-fibered-Σ-Decomposition D)))
      ( map-is-finite-displayed-fibered-Σ-Decomposition)
      ( map-inv-is-finite-displayed-fibered-Σ-Decomposition)

equiv-displayed-fibered-Σ-Decomposition-𝔽 :
  {l1 l : Level} (A : 𝔽 l1) →
  fibered-Σ-Decomposition-𝔽 l l l l A ≃ displayed-Σ-Decomposition-𝔽 l l l l A
equiv-displayed-fibered-Σ-Decomposition-𝔽 A =
  equiv-displayed-Σ-Decomposition-𝔽-is-finite-subtype A ∘e
    ( equiv-Σ
        ( λ x → type-Prop (is-finite-displayed-Σ-Decomposition A x))
        ( equiv-displayed-fibered-Σ-Decomposition)
        ( equiv-is-finite-displayed-fibered-Σ-Decomposition A) ∘e
      inv-equiv ( equiv-fibered-Σ-Decomposition-𝔽-is-finite-subtype A))
```
