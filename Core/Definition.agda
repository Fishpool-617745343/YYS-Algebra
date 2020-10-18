module Definition where

open import Relation.Binary.PropositionalEquality

-- YYS-Algebra
data YYS : Set where
  yy : YYS
  _s : YYS → YYS

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

_+ʸ_ : YYS → YYS → YYS
yy +ʸ yy = yy
yy +ʸ (y s) = y s
(y₁ s) +ʸ y₂ = (y₁ +ʸ y₂) s

infixl 6 _+ʸ_

Identityʸₗ : {A : Set} → A → Op₂ A → Set _
Identityʸₗ e _∙_ = ∀ x → (e ∙ x) ≡ x

Identityʸᵣ : {A : Set} → A → Op₂ A → Set _
Identityʸᵣ e _∙_ = ∀ x → (x ∙ e) ≡ x

Associateʸ : {A : Set} → Op₂ A → Set _
Associateʸ _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
