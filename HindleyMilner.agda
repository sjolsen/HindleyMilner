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

  _≡[_/_]₀_ : Type → Type → TypeVariable → Type → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)
  τ′ ≡[ υ / β ]₀ τ = τ′ ≡ₜ ([ υ / β ]₀ τ)

  _≡[_/_]_ : ∀ {n} → Type → Type → TypeVariable → TypeScheme n → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁)
  τ′ ≡[ υ / β ] σ = τ′ ≡ₜ ([ υ / β ] σ)


  data _instantiates_given_ : ∀ {n}
                            → Type
                            → TypeScheme n
                            → Vec Type n
                            → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Mono : ∀ {τ′ τ}
         → τ′ ≡ₜ τ
         → τ′ instantiates (Forall nil τ) given nil
    Poly : ∀ {τ″ τ′ υ₀ α₀ τ n} {υₛ : Vec Type n} {αₛ : Quantifiers n}
         → τ″ ≡[ υ₀ / α₀ ] (Forall αₛ τ′)
         → τ′ instantiates (Forall          αₛ  τ) given          υₛ
         → τ″ instantiates (Forall (cons α₀ αₛ) τ) given (cons υ₀ υₛ)


  -- int→int instantiates ∀α.α→α given [int]
  -- postulate
  --   int : PrimitiveType
  --   α β : TypeVariable

  -- foo : Func (Prim int) (Prim int) instantiates
  --       Forall (cons α nil) (Func (TVar α) (TVar α)) given
  --       (cons (Prim int) nil)
  -- foo = Poly (Func lemma lemma) (Mono ≡ₜ-refl)
  --   where lemma : Prim int ≡ₜ ([ Prim int / α ]₀ TVar α)
  --         lemma with α ≟ₜᵥ α
  --         ... | yes _ = Prim ≡ᵢ-refl
  --         ... | no  n = contradiction ≡ₜᵥ-refl n

  -- -- β→β instantiates ∀α.α→α given [β]
  -- bar : Func (TVar β) (TVar β) instantiates
  --       Forall (cons α nil) (Func (TVar α) (TVar α)) given
  --       (cons (TVar β) nil)
  -- bar = Poly (Func lemma lemma) (Mono ≡ₜ-refl)
  --   where lemma : TVar β ≡ₜ ([ TVar β / α ]₀ TVar α)
  --         lemma with α ≟ₜᵥ α
  --         ... | yes _ = TVar ≡ₜᵥ-refl
  --         ... | no  n = contradiction ≡ₜᵥ-refl n


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
  open import Relation.Binary

  replace-refl₀ : ∀ {τ β} → τ ≡[ TVar β / β ]₀ τ
  replace-refl₀ {TVar α} {β} with α ≟ₜᵥ β
  ... | yes α≡β = TVar α≡β
  ... | no  α≢β = TVar ≡ₜᵥ-refl
  replace-refl₀ {Prim ι}     = Prim ≡ᵢ-refl
  replace-refl₀ {Func τ₀ τ₁} = Func replace-refl₀ replace-refl₀

  replace-refl : ∀ {n τ β} {αₛ : Quantifiers n} → τ ≡[ TVar β / β ] Forall αₛ τ
  replace-refl {αₛ = nil} = replace-refl₀
  replace-refl {τ = τ} {β = β} {αₛ = cons α₀ αₛ} with β ∈freeₙ? (Forall (cons α₀ αₛ) τ)
  ... | yes _ = replace-refl {αₛ = αₛ}
  ... | no  _ = ≡ₜ-refl

  instantiates-refl : ∀ {n τ} {αₛ : Quantifiers n} → τ instantiates Forall αₛ τ given (vmap TVar αₛ)
  instantiates-refl         {αₛ =        nil} = Mono ≡ₜ-refl
  instantiates-refl {τ = τ} {αₛ = cons α₀ αₛ} = Poly (replace-refl {αₛ = αₛ}) instantiates-refl

  all∉freeₙ-refl : ∀ {n τ} {αₛ : Quantifiers n} → αₛ all∉freeₙ Forall αₛ τ
  all∉freeₙ-refl         {αₛ = nil}        = nil
  all∉freeₙ-refl {τ = τ} {αₛ = cons α₀ αₛ} = cons (∈freeₙ-elimₗ (flip _$_ ≡ₜᵥ-refl))
                                                  (all-map ∈freeₙ-elimᵣ all∉freeₙ-refl)

  ⊑-refl : ∀ {n} → Reflexive (_⊑_ {n = n})
  ⊑-refl {x = Forall          nil τ} = ⊑-intro (Mono ≡ₜ-refl) nil
  ⊑-refl {x = Forall (cons α₀ αₛ) τ} = ⊑-intro instantiates-refl all∉freeₙ-refl



  open import Data.Product

  instantiates-resp-≡ᵣ : ∀ {υ τ φ n}
                           {αₛ : Quantifiers n}
                           {υ→φ : Vec Type n}
                       → υ ≡ₜ τ
                       → φ instantiates Forall αₛ υ given υ→φ
                       → φ instantiates Forall αₛ τ given υ→φ
  instantiates-resp-≡ᵣ {αₛ = nil}        υ≡τ (Mono φ≡υ)                 = Mono (≡ₜ-trans φ≡υ υ≡τ)
  instantiates-resp-≡ᵣ {αₛ = cons α₀ αₛ} υ≡τ (Poly φ-α₀υ-υ→φ φ-αₛυ-υ→φ) = Poly φ-α₀υ-υ→φ (instantiates-resp-≡ᵣ υ≡τ φ-αₛυ-υ→φ)

  subs-nonfree-equiv : ∀ {τ υ φ β n}
                         {αₛ : Quantifiers n}
                     → υ ≡[ φ / β ] Forall αₛ τ
                     → β ∉freeₙ Forall αₛ τ
                     → υ ≡ₜ τ
  subs-nonfree-equiv {τ = TVar α} {β = β} {αₛ = nil} x y with α ≟ₜᵥ β
  ... | yes p = contradiction (Mono (TVar (≡ₜᵥ-sym p))) y
  ... | no ¬p = x
  subs-nonfree-equiv {Prim ι} {αₛ = nil} (Prim x) y = Prim x
  subs-nonfree-equiv {Func τ₀ τ₁} {β = β} {αₛ = nil} (Func x₀ x₁) y with β ∈free₀? τ₀ | β ∈free₀? τ₁
  ... | yes p₀ | _      = contradiction (Mono (Funcₗ p₀)) y
  ... | _      | yes p₁ = contradiction (Mono (Funcᵣ p₁)) y
  ... | no ¬p₀ | no ¬p₁ = Func (subs-nonfree-equiv x₀ ¬p₀′)
                               (subs-nonfree-equiv x₁ ¬p₁′)
    where ¬p₀′ : β ∉freeₙ Forall nil τ₀
          ¬p₀′ (Mono x) = ¬p₀ x
          ¬p₁′ : β ∉freeₙ Forall nil τ₁
          ¬p₁′ (Mono x) = ¬p₁ x
  subs-nonfree-equiv {τ} {υ} {φ} {β} {αₛ = cons α₀ αₛ} x y with β ∈freeₙ? Forall (cons α₀ αₛ) τ
  ... | yes p = contradiction p y
  ... | no ¬p = x

  instantiates-nonfree-irrel : ∀ {τ υ n}
                                 {αₛ : Quantifiers n}
                                 {τ→υ : Vec Type n}
                             → υ instantiates Forall αₛ τ given τ→υ
                             → αₛ all∉freeₙ Forall nil τ
                             → υ ≡ₜ τ
  instantiates-nonfree-irrel (Mono υ≡τ) _ = υ≡τ
  instantiates-nonfree-irrel {τ = τ} {αₛ = cons α₀ αₛ} (Poly x₀ xₛ) (cons y₀ yₛ) = ≡ₜ-trans {!!}
                                                                                            (instantiates-nonfree-irrel xₛ yₛ)

  instantiates-trans : ∀ {τ υ φ n₁ n₂}
                         {αₛ : Quantifiers n₁}
                         {βₛ : Quantifiers n₂}
                         {τ→υ : Vec Type n₁}
                         {υ→φ : Vec Type n₂}
                     → βₛ all∉freeₙ Forall αₛ τ
                     → υ instantiates Forall αₛ τ given τ→υ
                     → φ instantiates Forall βₛ υ given υ→φ
                     → Σ[ τ→φ ∈ Vec Type n₁ ] φ instantiates Forall αₛ τ given τ→φ
  instantiates-trans {αₛ  = nil}
                     {βₛ  = nil}
                     {υ→φ = nil}
                     βₛ-αₛτ
                     (Mono υ≡τ)
                     φ-βₛυ-υ→φ
                       = nil , instantiates-resp-≡ᵣ υ≡τ φ-βₛυ-υ→φ
  instantiates-trans {τ   = τ}
                     {αₛ  = nil}
                     {βₛ  = cons β₀ βₛ}
                     {υ→φ = cons υ→φ₀ υ→φₛ}
                     (cons β₀-αₛτ βₛ-αₛτ)
                     (Mono υ≡τ)
                     (Poly φ-β₀υ-υ→φ φ-βₛυ-υ→φ)
                       with β₀ ∈freeₙ? Forall nil τ
  ... | yes y = contradiction y β₀-αₛτ
  ... | no  n = nil , Mono {!!}
  instantiates-trans {αₛ = cons α₀ αₛ}
                     βₛ-αₛτ
                     υ-αₛτ-τ→υ
                     φ-βₛυ-υ→φ
                       = {!!}

  all∉freeₙ-trans : ∀ {τ υ n₁ n₂}
                      {αₛ : Quantifiers n₁}
                      {βₛ : Quantifiers n₂}
                      {γₛ : Quantifiers n₂}
                  → βₛ all∉freeₙ Forall αₛ τ
                  → γₛ all∉freeₙ Forall βₛ υ
                  → γₛ all∉freeₙ Forall αₛ τ
  all∉freeₙ-trans βₛ∉αₛτ γₛ∉βₛυ = {!!}

  ⊑-trans : ∀ {n} → Transitive (_⊑_ {n = n})
  ⊑-trans {i = Forall αₛ τ}
          {j = Forall βₛ υ}
          {k = Forall γₛ φ}
          (⊑-intro {n = n} {τₛ = τ→υ} υ-αₛτ-τ→υ βₛ∉αₛτ)
          (⊑-intro         {τₛ = υ→φ} φ-βₛυ-υ→φ γₛ∉βₛυ)
    = ⊑-intro (proj₂ (instantiates-trans βₛ∉αₛτ υ-αₛτ-τ→υ φ-βₛυ-υ→φ))
              (all∉freeₙ-trans βₛ∉αₛτ γₛ∉βₛυ)


  data _≈_ : ∀ {n} (σ σ′ : TypeScheme n) → Set (c₀ ⊔ c₁ ⊔ ℓ₀ ⊔ ℓ₁) where
    Bidir : ∀ {n} {σ σ′ : TypeScheme n}
          → σ  ⊑  σ′
          → σ′ ⊑  σ
          → σ  ≈  σ′

  ≈-refl : ∀ {n} → Reflexive (_≈_ {n = n})
  ≈-refl = Bidir ⊑-refl ⊑-refl

  ≈-sym : ∀ {n} → Symmetric (_≈_ {n = n})
  ≈-sym (Bidir i⊑j j⊑i) = Bidir j⊑i i⊑j

  ≈-trans : ∀ {n} → Transitive (_≈_ {n = n})
  ≈-trans (Bidir i⊑j j⊑i) (Bidir j⊑k k⊑j) = Bidir (⊑-trans i⊑j j⊑k) (⊑-trans k⊑j j⊑i)

  ⊑-antisym : ∀ {n} → Antisymmetric (_≈_ {n = n}) _⊑_
  ⊑-antisym x⊑y y⊑x = Bidir x⊑y y⊑x
