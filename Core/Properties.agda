module Properties where

open import Relation.Binary.PropositionalEquality
open import Definition
open import Function

idʸₗ : Identityʸₗ yy _+ʸ_
idʸₗ  yy   = refl
idʸₗ (_ s) = refl

idʸᵣ : Identityʸᵣ yy _+ʸ_
idʸᵣ  yy   = refl
idʸᵣ (y s) = cong _s (idʸᵣ y)

sucʸ : ∀ {x y : YYS} → (x s) +ʸ y ≡ (x +ʸ y) s
sucʸ = refl

assocʸ : Associateʸ _+ʸ_
assocʸ yy y z rewrite idʸₗ y | idʸₗ (y +ʸ z) = refl
assocʸ (x s) y z = cong _s (assocʸ x y z)
