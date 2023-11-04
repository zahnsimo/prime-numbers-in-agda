module divRem where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary.Definitions hiding (Decidable)
--open import Relation.Binary.Reasoning.StrictPartialOrder
open import Relation.Unary using (Decidable)

private variable
  d k l m n o p : ℕ

A⊎B⇒¬A⇒B : {A B : Set} → A ⊎ B → ¬ A → B
A⊎B⇒¬A⇒B (inj₁ a) ¬a = ⊥-elim (¬a a)
A⊎B⇒¬A⇒B (inj₂ b) _  = b

------division with remainder
------goal : n = r + q * m , r < m


divRem : (m n : ℕ) → m ≡ 0 ⊎ Σ (ℕ × ℕ) (λ (q , r) → r < m × n ≡ r + q * m)
divRem zero n  = inj₁ refl
divRem m@(suc _) zero  = inj₂ ((0 , 0) , ((s≤s z≤n) , refl)) --(0 , (0 , ((s≤s z≤n) , refl)))
divRem m@(suc _) (suc n)  with divRem m n
... | inj₁ e = inj₁ e
... | inj₂ ((q , r) , r<m , eq) = case suc r ≟ m of λ
  { (no sr≢m)  → inj₂ ( (q     , suc r) , ≤∧≢⇒< r<m sr≢m , cong suc eq )
  ; (yes sr≡m) → inj₂ ( (suc q , 0    ) , (s≤s z≤n)  , trans (cong suc eq) (cong (_+ q * m) sr≡m) ) }


divRemUnique : (m n : ℕ) → m ≡ 0 ⊎ ∃! {A = ℕ × ℕ}  _≡_ λ (q , r) → r < m × n ≡ r + q * m
divRemUnique zero n = inj₁ refl
divRemUnique m@(suc _) n with divRem m n
... | inj₂ ((q , r) , r<m , eq)
  = let lemma = λ q q' r r' (r<m : r < m) (eq : n ≡ r + q * m) (eq' : n ≡ r' + q' * m) (q<q' : q < q') → let open ≤-Reasoning in
                              begin suc n         ≡⟨ cong suc eq ⟩
                                    suc r + q * m ≤⟨ +-monoˡ-≤ (q * m) r<m ⟩
                                    suc q * m     ≤⟨ *-monoˡ-≤ m q<q' ⟩
                                    q' * m        ≤⟨ +-monoˡ-≤ (q' * m) (z≤n {r'}) ⟩
                                    r' + q' * m   ≡⟨ sym eq' ⟩
                                    n ∎
        unique-q = λ q q' r r' (r<m : r < m) (r'<m : r' < m) (eq : n ≡ r + q * m) (eq' : n ≡ r' + q' * m) →
                               case <-cmp q q' of λ
                                 { (tri< q<q' q≢q' q≯q') → ⊥-elim (n≮n n (lemma q q' r r' r<m eq eq' q<q'))
                                 ; (tri≈ q≮q' q≡q' q≯q') → q≡q'
                                 ; (tri> q≮q' q≢q' q>q') → ⊥-elim (n≮n n (lemma q' q r' r r'<m eq' eq q>q') )
                                 }
        unique-r = λ q q' (q≡q' : q ≡ q') r r' (eq : n ≡ r + q * m) (eq' : n ≡ r' + q' * m) → let open ≡-Reasoning in
                               +-cancelʳ-≡ _ _ (
                                 begin r  + q  * m ≡⟨ sym eq ⟩
                                       n           ≡⟨ eq' ⟩
                                       r' + q' * m ≡⟨ cong (λ q → r' + q * m) (sym q≡q') ⟩
                                       r' + q  * m ∎
                                               )
    in inj₂ ((q , r) , (r<m , eq) , λ where {(q' , r')} (r'<m , eq') →
                                                 let q≡q' = unique-q q q' r r' r<m r'<m eq eq'
                                                     r≡r' = unique-r q q' q≡q' r r' eq eq'
                                                 in  Inverse.f ×-≡,≡↔≡ (q≡q' , r≡r'))

divRemUnique' : (m n : ℕ) → m ≢ 0 → ∃! {A = ℕ × ℕ} _≡_ λ (q , r) → r < m × n ≡ r + q * m 
divRemUnique' m n m≢0 = A⊎B⇒¬A⇒B (divRemUnique m n) m≢0

rem : (m n : ℕ) → m ≢ 0 → ℕ
rem m n e = proj₂ (proj₁ (divRemUnique' m n e))


