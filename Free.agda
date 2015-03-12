open import Relation.Binary using (DecSetoid)
module Free {c₀ ℓ₀} (primitiveType : DecSetoid c₀ ℓ₀)
            {c₁ ℓ₁} (typeVariable  : DecSetoid c₁ ℓ₁) where
  open import Core primitiveType typeVariable
  open import Type primitiveType typeVariable
  open import Util
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Binary



  data _∈free₀_ (α : TypeVariable) : Type → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    TVar  : {β : TypeVariable} → α ≡ₜᵥ β     → α ∈free₀ TVar β
    Funcₗ : {τ₀ τ₁ : Type}     → α ∈free₀ τ₀ → α ∈free₀ Func τ₀ τ₁
    Funcᵣ : {τ₀ τ₁ : Type}     → α ∈free₀ τ₁ → α ∈free₀ Func τ₀ τ₁

  private
    ∈free₀-elim₀ : ∀ {α β} {p} {P : Set p}
                 → (α ≡ₜᵥ β         → P)
                 → (α ∈free₀ TVar β → P)
    ∈free₀-elim₀ p (TVar α≡β) = p α≡β

    ∈free₀-elim₂ : ∀ {α τ₀ τ₁} {p} {P : Set p}
                 → (α ∈free₀ τ₀         → P)
                 → (α ∈free₀ τ₁         → P)
                 → (α ∈free₀ Func τ₀ τ₁ → P)
    ∈free₀-elim₂ p₁ _ (Funcₗ α∈freeτ₀) = p₁ α∈freeτ₀
    ∈free₀-elim₂ _ p₂ (Funcᵣ α∈freeτ₁) = p₂ α∈freeτ₁

  _∈free₀?_ : Decidable _∈free₀_
  α ∈free₀? TVar β     = if? (α ≟ₜᵥ β)
                           (λ α≡β → yes (TVar α≡β))
                           (λ α≢β → no  (∈free₀-elim₀ α≢β))
  α ∈free₀? Prim ι     = no (λ ())
  α ∈free₀? Func τ₀ τ₁ = if₂? (α ∈free₀? τ₀)
                              (α ∈free₀? τ₁)
                           (λ y₀ y₁ → yes (Funcₗ y₀))
                           (λ y₀ n₁ → yes (Funcₗ y₀))
                           (λ n₀ y₁ → yes (Funcᵣ y₁))
                           (λ n₀ n₁ → no  (∈free₀-elim₂ n₀ n₁))



  data _∈freeₙ_ (α : TypeVariable) : ∀ {n} → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono : {τ : Type}
         → α ∈free₀ τ
         → α ∈freeₙ (Forall nil τ)
    Poly : ∀ {n}
         → {β₀ : TypeVariable}
           {βₛ : Quantifiers n}
           {τ : Type}
         → α ≢ₜᵥ β₀
         → α ∈freeₙ (Forall βₛ           τ)
         → α ∈freeₙ (Forall (cons β₀ βₛ) τ)

  private
    ∈freeₙ-elim₀ : ∀ {α τ} {p} {P : Set p}
                 → (α ∈free₀ τ              → P)
                 → (α ∈freeₙ (Forall nil τ) → P)
    ∈freeₙ-elim₀ p (Mono α∈freeτ) = p α∈freeτ

    ∈freeₙ-elimₗ : ∀ {α τ n β₀} {βₛ : Quantifiers n} {p} {P : Set p}
                 → (α ≢ₜᵥ β₀                         → P)
                 → (α ∈freeₙ (Forall (cons β₀ βₛ) τ) → P)
    ∈freeₙ-elimₗ p (Poly α≢β _) = p α≢β

    ∈freeₙ-elimᵣ : ∀ {α τ n β₀} {βₛ : Quantifiers n} {p} {P : Set p}
                 → (α ∈freeₙ (Forall βₛ           τ) → P)
                 → (α ∈freeₙ (Forall (cons β₀ βₛ) τ) → P)
    ∈freeₙ-elimᵣ p (Poly _ α∈freeβ) = p α∈freeβ

  _∈freeₙ?_ : ∀ {n} (α : TypeVariable) (σ : TypeScheme n) → Dec (α ∈freeₙ σ)
  α ∈freeₙ? Forall nil          τ = if? (α ∈free₀? τ)
                                      (λ y → yes (Mono y))
                                      (λ n → no  (∈freeₙ-elim₀ n))
  α ∈freeₙ? Forall (cons β₀ βₛ) τ = if₂? (α ≟ₜᵥ β₀)
                                         (α ∈freeₙ? Forall βₛ τ)
                                      (λ α≡β y → no (∈freeₙ-elimₗ (contradiction α≡β)))
                                      (λ α≡β n → no (∈freeₙ-elimₗ (contradiction α≡β)))
                                      (λ α≢β y → yes (Poly α≢β y))
                                      (λ α≢β n → no (∈freeₙ-elimᵣ n))
