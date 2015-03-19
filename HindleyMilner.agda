open import Relation.Binary using (DecSetoid)
module HindleyMilner {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
                     {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Free primitiveType typeVariable



  open import Relation.Nullary
  open import Relation.Nullary.Negation

  [_/_]₀_ : Type → TypeVariable → Type → Type
  [ υ / β ]₀ TVar α with α ≟ₜᵥ β
  ... | yes _ = υ
  ... | no  _ = TVar α
  [ υ / β ]₀ Prim ι = Prim ι
  [ υ / β ]₀ Func τ₀ τ₁ = Func ([ υ / β ]₀ τ₀) ([ υ / β ]₀ τ₁)

  [_/_]_ : ∀ {n} → Type → TypeVariable → TypeScheme n → Type
  [ υ / β ] Forall nil          τ = [ υ / β ]₀ τ
  [ υ / β ] Forall (cons α₀ αₛ) τ with β ∈freeₙ? (Forall (cons α₀ αₛ) τ)
  ... | yes _ = [ υ / β ] Forall αₛ τ
  ... | no  _ = τ



  open import Util

  _≈[_/_]₀_ : Type → Type → TypeVariable → Type → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)
  τ′ ≈[ υ / β ]₀ τ = τ′ ≡ₜ ([ υ / β ]₀ τ)

  _≈[_/_]_ : ∀ {n} → Type → Type → TypeVariable → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)
  τ′ ≈[ υ / β ] σ = τ′ ≡ₜ ([ υ / β ] σ)


  data _instantiates_given_ : ∀ {n}
                            → Type
                            → TypeScheme n
                            → Vec Type n
                            → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono : ∀ {τ}
         → τ instantiates (Forall nil τ) given nil
    Poly : ∀ {τ″ τ′ υ₀ α₀ τ n} {υₛ : Vec Type n} {αₛ : Quantifiers n}
         → τ″ ≈[ υ₀ / α₀ ] (Forall αₛ τ′)
         → τ′ instantiates (Forall          αₛ  τ) given          υₛ
         → τ″ instantiates (Forall (cons α₀ αₛ) τ) given (cons υ₀ υₛ)


  -- int→int instantiates ∀α.α→α given [int]
  postulate
    int : PrimitiveType
    α β : TypeVariable

  foo : Func (Prim int) (Prim int) instantiates
        Forall (cons α nil) (Func (TVar α) (TVar α)) given
        (cons (Prim int) nil)
  foo = Poly (Func lemma lemma) Mono
    where lemma : Prim int ≡ₜ ([ Prim int / α ]₀ TVar α)
          lemma with α ≟ₜᵥ α
          ... | yes _ = Prim ≡ᵢ-refl
          ... | no  n = contradiction ≡ₜᵥ-refl n

  -- β→β instantiates ∀α.α→α given [β]
  bar : Func (TVar β) (TVar β) instantiates
        Forall (cons α nil) (Func (TVar α) (TVar α)) given
        (cons (TVar β) nil)
  bar = Poly (Func lemma lemma) Mono
    where lemma : TVar β ≡ₜ ([ TVar β / α ]₀ TVar α)
          lemma with α ≟ₜᵥ α
          ... | yes _ = TVar ≡ₜᵥ-refl
          ... | no  n = contradiction ≡ₜᵥ-refl n


  open import Data.Product
  open import Function

  _all∉freeₙ_ : ∀ {m n} → Vec TypeVariable m → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)
  αₛ all∉freeₙ σ = all (flip _∉freeₙ_ σ) αₛ


  data _⊑_ : ∀ {m n} → TypeScheme m → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    ⊑-intro : ∀ {n m τ τ′ τₛ}
                {αₛ : Quantifiers n}
                {βₛ : Quantifiers m}
            → τ′ instantiates (Forall αₛ τ) given τₛ
            → βₛ all∉freeₙ (Forall αₛ τ)
            → (Forall αₛ τ) ⊑ (Forall βₛ τ′)

  private
    ⊑-elim₀ : ∀ {n m τ τ′}
                {αₛ : Quantifiers n}
                {βₛ : Quantifiers m}
            → (Forall αₛ τ) ⊑ (Forall βₛ τ′)
            → Σ[ τₛ ∈ Vec Type n ] τ′ instantiates (Forall αₛ τ) given τₛ
    ⊑-elim₀ (⊑-intro {τₛ = τₛ} x _) = τₛ , x

    ⊑-elim₁ : ∀ {n m τ τ′}
                {αₛ : Quantifiers n}
                {βₛ : Quantifiers m}
            → (Forall αₛ τ) ⊑ (Forall βₛ τ′)
            → βₛ all∉freeₙ (Forall αₛ τ)
    ⊑-elim₁ (⊑-intro _ x) = x


  open import Relation.Nullary

  replace-refl₀ : ∀ {τ β} → τ ≈[ TVar β / β ]₀ τ
  replace-refl₀ {TVar α} {β} with α ≟ₜᵥ β
  ... | yes α≡β = TVar α≡β
  ... | no  α≢β = TVar ≡ₜᵥ-refl
  replace-refl₀ {Prim ι}     = Prim ≡ᵢ-refl
  replace-refl₀ {Func τ₀ τ₁} = Func replace-refl₀ replace-refl₀

  replace-refl : ∀ {n τ β} {αₛ : Quantifiers n} → τ ≈[ TVar β / β ] Forall αₛ τ
  replace-refl {αₛ = nil} = replace-refl₀
  replace-refl {τ = τ} {β = β} {αₛ = cons α₀ αₛ} with β ∈freeₙ? (Forall (cons α₀ αₛ) τ)
  ... | yes _ = replace-refl {αₛ = αₛ}
  ... | no  _ = ≡ₜ-refl

  instantiates-refl : ∀ {n τ} {αₛ : Quantifiers n} → τ instantiates Forall αₛ τ given (vmap TVar αₛ)
  instantiates-refl         {αₛ =        nil} = Mono
  instantiates-refl {τ = τ} {αₛ = cons α₀ αₛ} = Poly (replace-refl {αₛ = αₛ}) instantiates-refl

  all∉freeₙ-refl : ∀ {n τ} {αₛ : Quantifiers n} → αₛ all∉freeₙ Forall αₛ τ
  all∉freeₙ-refl         {αₛ = nil}        = nil
  all∉freeₙ-refl {τ = τ} {αₛ = cons α₀ αₛ} = cons (∈freeₙ-elimₗ (flip _$_ ≡ₜᵥ-refl))
                                                  (all-map ∈freeₙ-elimᵣ all∉freeₙ-refl)

  -- Reflexive
  ⊑-refl : ∀ {n} {σ : TypeScheme n} → σ ⊑ σ
  ⊑-refl {σ = Forall          nil τ} = ⊑-intro Mono nil
  ⊑-refl {σ = Forall (cons α₀ αₛ) τ} = ⊑-intro instantiates-refl all∉freeₙ-refl
