open import Relation.Binary using (DecSetoid)
module HindleyMilner {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
                     {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Free primitiveType typeVariable



  open import Util

  data _≈[_/_]₀_ : Type
                 → Type → TypeVariable
                 → Type
                 → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    TVar₀ : ∀ {α υ β} → α ≢ₜᵥ β → TVar α ≈[ υ / β ]₀ TVar α
    TVar₁ : ∀ {α υ β} → α ≡ₜᵥ β → TVar α ≈[ υ / β ]₀ υ
    Prim  : ∀ {ι υ β}           → Prim ι ≈[ υ / β ]₀ Prim ι
    Func  : ∀ {τ₀ τ₁ τ₂ τ₃ υ β}
          → τ₀ ≈[ υ / β ]₀ τ₂
          → τ₁ ≈[ υ / β ]₀ τ₃
          → Func τ₀ τ₁ ≈[ υ / β ]₀ Func τ₂ τ₃

  data _≈[_/_]_ : ∀ {n} → TypeScheme n
                        → Type → TypeVariable
                        → TypeScheme n
                        → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono  : ∀ {τ υ β τ′}
          →            τ ≈[ υ / β ]₀            τ′
          → Forall nil τ ≈[ υ / β ]  Forall nil τ′
    Poly₀ : ∀ {τ υ β n} {αₛ : Quantifiers (suc n)}
          → β ∉freeₙ (Forall αₛ τ)
          → Forall αₛ τ ≈[ υ / β ] Forall αₛ τ
    Poly₁ : ∀ {τ υ β τ′ n α₀} {αₛ : Quantifiers n}
          → β ∈freeₙ (Forall (cons α₀ αₛ) τ)
          → Forall          αₛ  τ ≈[ υ / β ] Forall          αₛ  τ′
          → Forall (cons α₀ αₛ) τ ≈[ υ / β ] Forall (cons α₀ αₛ) τ′


  data _instantiates_given_ : ∀ {n}
                            → Type
                            → TypeScheme n
                            → Vec Type n
                            → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono : ∀ {τ}
         → τ instantiates (Forall nil τ) given nil
    Poly : ∀ {τ″ τ′ υ₀ α₀ τ n} {υₛ : Vec Type n} {αₛ : Quantifiers n}
         → (Forall αₛ τ′) ≈[ υ₀ / α₀ ] (Forall αₛ τ″)
         → τ′ instantiates (Forall          αₛ  τ) given          υₛ
         → τ″ instantiates (Forall (cons α₀ αₛ) τ) given (cons υ₀ υₛ)


  -- int→int instantiates ∀α.α→α given [int]
  postulate
    int : PrimitiveType
    α β : TypeVariable

  foo : Func (Prim int) (Prim int) instantiates
        Forall (cons α nil) (Func (TVar α) (TVar α)) given
        (cons (Prim int) nil)
  foo = Poly (Mono (Func (TVar₁ ≡ₜᵥ-refl) (TVar₁ ≡ₜᵥ-refl))) Mono

  -- β→β instantiates ∀α.α→α given [β]
  bar : Func (TVar β) (TVar β) instantiates
        Forall (cons α nil) (Func (TVar α) (TVar α)) given
        (cons (TVar β) nil)
  bar = Poly (Mono (Func (TVar₁ ≡ₜᵥ-refl) (TVar₁ ≡ₜᵥ-refl))) Mono


  open import Data.Product
  open import Relation.Nullary.Negation
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

  replace-refl : ∀ {n τ β} {αₛ : Quantifiers n} → Forall αₛ τ ≈[ TVar β / β ] Forall αₛ τ
  replace-refl {τ = TVar α} {β = β} {αₛ = nil} with α ≟ₜᵥ β
  ... | yes α≡β = Mono {!TVar₁ α≡β!} -- Gives TVar α ≈[ TVar β / β ]₀ TVar β
                                     -- Need  TVar α ≈[ TVar β / β ]₀ TVar α
  ... | no  α≢β = Mono (TVar₀ α≢β)
  replace-refl {τ = Prim ι} {β = β} {αₛ = nil} = {!!}
  replace-refl {τ = Func τ₀ τ₁} {β = β} {αₛ = nil} = {!!}
  replace-refl {τ = τ} {β = β} {αₛ = cons α₀ αₛ} = {!!}

  instantiates-refl : ∀ {n τ} {αₛ : Quantifiers n} → τ instantiates Forall αₛ τ given (vmap TVar αₛ)
  instantiates-refl         {αₛ =        nil} = Mono
  instantiates-refl {τ = τ} {αₛ = cons α₀ αₛ} with α₀ ∈freeₙ? (Forall αₛ τ)
  ... | yes y = Poly {τ′ = τ} {!!} instantiates-refl
  ... | no  n = Poly {τ′ = τ} {!!} instantiates-refl

  -- Reflexive
  ⊑-refl : ∀ {n} {σ : TypeScheme n} → σ ⊑ σ
  ⊑-refl {σ = Forall          nil τ} = ⊑-intro Mono nil
  ⊑-refl {σ = Forall (cons α₀ αₛ) τ} = ⊑-intro {!!} {!!}
