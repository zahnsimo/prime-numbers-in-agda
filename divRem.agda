module divRem where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary.Definitions hiding (Decidable)
--open import Relation.Binary.Reasoning.StrictPartialOrder
open import Relation.Unary using (Decidable)

variable
  d k l m n o p : ℕ


A⊎B→¬A→B : {A B : Set} → A ⊎ B → ¬ A → B
A⊎B→¬A→B (inj₁ a) ¬a = ⊥-elim (¬a a)
A⊎B→¬A→B (inj₂ b) _  = b

------division with remainder
------goal : n = r + q * m , r < m


divRem : (m n : ℕ) → m ≡ 0 ⊎ ∃[ q ] ∃[ r ] r < m × n ≡ r + q * m
divRem zero n  = inj₁ refl
divRem m@(suc _) zero  = inj₂ (0 , (0 , ((s≤s z≤n) , refl)))
divRem m@(suc _) (suc n)  with divRem m n
... | inj₁ e = inj₁ e
... | inj₂ (q , r , r<m , eq) = case suc r ≟ m of λ
  { (no sr≢m)  → inj₂ ( q     , suc r , ≤∧≢⇒< r<m sr≢m , cong suc eq )
  ; (yes sr≡m) → inj₂ ( suc q , 0     , (s≤s z≤n)  , trans (cong suc eq) (cong (_+ q * m) sr≡m) ) }

open ≤-Reasoning
divRemUniqueQ : (m n : ℕ) → m ≡ 0 ⊎ ∃! _≡_ λ q → ( ∃[ r ] r < m × n ≡ r + q * m )
divRemUniqueQ zero n = inj₁ refl
divRemUniqueQ m@(suc _) n  with divRem m n
... | inj₂ (q , r , r<m , eq) = inj₂ (q , ((r , (r<m , eq)) , 
  (λ where {q'} (r' , (r'<m , eq')) →
                let lemma = λ q q' r r' (r<m : r < m) (eq : n ≡ r + q * m) (eq' : n ≡ r' + q' * m) (q<q' : q < q') →
                              begin suc n         ≡⟨ cong suc eq ⟩
                                    suc r + q * m ≤⟨ +-monoˡ-≤ (q * m) r<m ⟩
                                    suc q * m     ≤⟨ *-monoˡ-≤ m q<q' ⟩
                                    q' * m        ≤⟨ +-monoˡ-≤ (q' * m) (z≤n {r'}) ⟩
                                    r' + q' * m   ≡⟨ sym eq' ⟩
                                    n ∎
                    in case <-cmp q q' of λ
                { (tri< q<q' q≢q' q≯q') → ⊥-elim (n≮n n (lemma q q' r r' r<m eq eq' q<q'))
                ; (tri≈ q≮q' q≡q' q≯q') → q≡q'
                ; (tri> q≮q' q≢q' q>q') → ⊥-elim (n≮n n (lemma q' q r' r r'<m eq' eq q>q') ) } )) )

divRemUniqueR : (m n : ℕ) → m ≡ 0 ⊎ ∃[ q ] ∃! _≡_ λ r → ( r < m × n ≡ r + q * m )
divRemUniqueR zero n = inj₁ refl
divRemUniqueR m@(suc _) n with divRem m n
... | inj₂ (q , r , r<m , eq) = inj₂ (q , (r , ((r<m , eq) ,
  λ {y} (y<m , eq_y) → +-cancelʳ-≡ r y (trans (sym eq) eq_y))))

divRemUnique : (m n : ℕ) → m ≡ 0 ⊎ ∃! _≡_ λ q → ( ∃! _≡_ λ r → ( r < m × n ≡ r + q * m ) )
divRemUnique zero n = inj₁ refl
divRemUnique m@(suc _) n with divRemUniqueQ m n
... | inj₂ (q , (r , r<m , eq) , uniqueQ) = inj₂ (q , ((r , ((r<m , eq)
  , λ { {r'} (r'<m , eq') → +-cancelʳ-≡ r r' (trans (sym eq) eq')}))     --uniqueness of r
  , λ { (r' , (r'<m , eq') , uniqueR) → uniqueQ (r' , (r'<m , eq'))}))   --uniqueness of q


divRem' : (m n : ℕ) → m ≢ 0 → ∃[ q ] ∃[ r ] r < m × n ≡ r + q * m
divRem' m n m≢0 with divRem m n
... | inj₁ m≡0 = ⊥-elim (m≢0 m≡0)
... | inj₂ x = x

divRemUniqueR' : (m n : ℕ) → m ≢ 0 → ∃[ q ] ∃! _≡_ λ r → ( r < m × n ≡ r + q * m )
divRemUniqueR' m n m≢0 with divRemUniqueR m n
... | inj₁ m≡0 = ⊥-elim (m≢0 m≡0)
... | inj₂ x = x

divRemUnique' : (m n : ℕ) → m ≢ 0 → ∃! _≡_ λ q → ( ∃! _≡_ λ r → ( r < m × n ≡ r + q * m ) )
divRemUnique' m n m≢0 with divRemUnique m n
... | inj₁ m≡0 = ⊥-elim (m≢0 m≡0)
... | inj₂ x = x
