open import Relation.Binary using (DecSetoid)
module HindleyMilner {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
                     {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Free primitiveType typeVariable



  open import Util

  data _≈[_/_]₀_ : Type → Type → TypeVariable → Type → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    TVar₀ : ∀ {α υ β} → α ≢ₜᵥ β → TVar α ≈[ υ / β ]₀ TVar α
    TVar₁ : ∀ {α υ β} → α ≡ₜᵥ β → TVar α ≈[ υ / β ]₀ υ
    Prim  : ∀ {ι υ β}           → Prim ι ≈[ υ / β ]₀ Prim ι
    Func  : ∀ {τ₀ τ₁ τ₂ τ₃ υ β}
          → τ₀ ≈[ υ / β ]₀ τ₂
          → τ₁ ≈[ υ / β ]₀ τ₃
          → Func τ₀ τ₁ ≈[ υ / β ]₀ Func τ₂ τ₃

  data _≈[_/_]_ : ∀ {n} → TypeScheme n → Type → TypeVariable → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono : ∀ {τ υ β τ′}
         →            τ ≈[ υ / β ]₀            τ′
         → Forall nil τ ≈[ υ / β ]  Forall nil τ′
    Poly₀ : ∀ {τ υ β n} {αₛ : Quantifiers (suc n)}
          → β ∉freeₙ (Forall αₛ τ)
          → Forall αₛ τ ≈[ υ / β ] Forall αₛ τ
    Poly₁ : ∀ {τ υ β τ′ n α₀} {αₛ : Quantifiers n}
          → β ∈freeₙ (Forall (cons α₀ αₛ) τ)
          → Forall          αₛ  τ ≈[ υ / β ] Forall          αₛ  τ′
          → Forall (cons α₀ αₛ) τ ≈[ υ / β ] Forall (cons α₀ αₛ) τ′
