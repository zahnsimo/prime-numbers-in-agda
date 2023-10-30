module prim where

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
open import Relation.Binary.Reasoning.StrictPartialOrder
open import Relation.Unary using (Decidable)

postulate
  lem : ∀ {A : Set} → A ⊎ ¬ A

variable
  d k l m n o p : ℕ

------first definition (additive)

data _∣_ : ℕ → ℕ → Set where

  --o∣n :  1 ∣ n

  m∣z   : m ∣ 0

  m∣m+n :  m ∣ n → m ∣ (m + n)


------second definition (multiplicative)

data _∣*_ : ℕ → ℕ → Set where

   m∣k*m : ∀ (k : ℕ) →  m ∣* (k * m)


------both definitions are equivalent

∣→∣* : (m ∣ n) → (m ∣* n)
∣→∣* m∣z = m∣k*m zero
∣→∣* (m∣m+n e) with ∣→∣* e
... | (m∣k*m k) = m∣k*m (suc k)


∣*→∣ : m ∣* n → m ∣ n
∣*→∣ (m∣k*m zero) = m∣z
∣*→∣ (m∣k*m (suc k)) = m∣m+n (∣*→∣ (m∣k*m k))


------some properties

m∣n-m : m ∣ n → m ≤ n → m ∣ (n ∸ m)
m∣n-m m∣z z≤n = m∣z
--m∣n-m (m∣m+n {m} {n} m∣n) _ rewrite m+n∸m≡n m n = m∣n
m∣n-m (m∣m+n {m} {n} m∣n) _ = subst (m ∣_) (sym (m+n∸m≡n m n)) m∣n

m∣n-m' : m ∣ n → m ∣ (n ∸ m)
m∣n-m' {m = zero} m∣z = m∣z
m∣n-m' {m = suc m} m∣z = m∣z
--m∣n-m' (m∣m+n {m} {n} m∣n) rewrite m+n∸m≡n m n = m∣n
m∣n-m' (m∣m+n {m} {n} m∣n) = subst (m ∣_) (sym (m+n∸m≡n m n)) m∣n

z∤s : ¬ (zero ∣ suc m)
z∤s (m∣m+n x) = z∤s x

z∤*s : ¬ (zero ∣* suc m)
z∤*s e = z∤s (∣*→∣ e)

o∣m : 1 ∣ m
o∣m {zero} = m∣z
o∣m {suc m} = m∣m+n o∣m

o∣*m : 1 ∣* m
o∣*m {m} = subst (1 ∣*_) (*-identityʳ m) (m∣k*m m)

m∣m : m ∣ m
m∣m {m} = subst (m ∣_) (+-identityʳ m) (m∣m+n {m} {0} m∣z)

m∣*m : m ∣* m
m∣*m {m} = subst (m ∣*_) (*-identityˡ m) (m∣k*m 1)

m∣n+m : m ∣ n → m ∣ (n + m)
m∣n+m {m} {n} m∣n = subst (m ∣_) (+-comm m n) (m∣m+n m∣n)

m∣m*k : ∀ (k : ℕ) → m ∣* (m * k)
m∣m*k {m} k = subst (m ∣*_) (*-comm k m) (m∣k*m k)

∣→≤ : m ∣ n → n ≡ 0 ⊎ m ≤ n
∣→≤ m∣z = inj₁ refl
∣→≤ (m∣m+n {m} {n} e) = inj₂ (m≤m+n m n)

∣→≤' : k ≡ suc n → m ∣ k  → m ≤ k
∣→≤' e (m∣m+n e') = m≤m+n _ _

∣→≤'' : m ∣ (suc n) → m ≤ (suc n)
∣→≤'' e = ∣→≤' refl e


∣*→≤ : m ∣* n → n ≡ 0 ⊎ m ≤ n
∣*→≤ (m∣k*m zero) = inj₁ refl
∣*→≤ (m∣k*m {m} (suc k)) = inj₂ (m≤m+n m (k * m))

∣*→≤' : ∀ {n₁ : ℕ} → (n ≡ suc n₁) → m ∣* n → m ≤ n
∣*→≤' e (m∣k*m {m} k) = m≤n*m m {!!}

∣*→≤'' : m ∣* (suc n) → m ≤ (suc n)
∣*→≤'' e = ∣*→≤' refl e

∣*→≤''' : (n ≢ 0) → m ∣* n → m ≤ n
∣*→≤''' n≢0 m∣*n = {!!}

∣*-trans : m ∣* n → n ∣* o → m ∣* o
∣*-trans (m∣k*m {m} k) (m∣k*m l) rewrite sym(*-assoc l k m) = m∣k*m (l * k)

∣-trans : m ∣ n → n ∣ o → m ∣ o
∣-trans e e'  = ∣*→∣ (∣*-trans (∣→∣* e) (∣→∣* e'))


--
{-# TERMINATING #-}

_∣?_ : (m n : ℕ) → Dec (m ∣ n)
m ∣? zero = yes m∣z
m ∣? n@(suc _) = case m ≤? n of λ { (no m≰n) → no λ m∣n → m≰n (∣→≤'' m∣n)
                                  ; (yes m≤n) → case m ∣? (n ∸ m) of λ {(no m∤n∸m) → no λ m∣n → m∤n∸m (m∣n-m' m∣n)
                                                                      ; (yes m∣n∸m) → yes (subst (m ∣_) (m+[n∸m]≡n {m} {n} m≤n) (m∣m+n m∣n∸m))} }


------division with remainder
------goal : n = r + q * m , r < m

divRem : (m n : ℕ) → m ≡ 0 ⊎ ∃[ q ] ∃[ r ] r < m × n ≡ r + q * m
divRem zero n  = inj₁ refl
divRem m@(suc _) zero  = inj₂ (0 , (0 , ((s≤s z≤n) , refl)))
divRem (suc m) (suc n)  with divRem (suc m) n
... | inj₁ e = inj₁ e
... | inj₂ (q , r , r<sm , eq) = case r ≟ m of λ
  { (no r≢m) → inj₂ ( q     , suc r , ≤∧≢⇒< r<sm (λ sr≡sm → r≢m (suc-injective sr≡sm)) , (cong suc eq) )
  ; (yes r≡m) → inj₂ ( suc q , 0     , (s≤s z≤n)  , cong suc (trans eq (cong (_+ (q * suc m)) r≡m)) ) }

divRemUniqueQ : (m n : ℕ) → m ≡ 0 ⊎ ∃! _≡_ λ q → ( ∃[ r ] r < m × n ≡ r + q * m )
divRemUniqueQ zero n = inj₁ refl
divRemUniqueQ (suc m) n  with divRem (suc m) n
... | inj₂ (q , r , r<sm , eq) = inj₂ (q , ((r , (r<sm , eq)) , 
  (λ where {q'} (r' , (r'<sm , eq')) → case <-cmp q q' of λ
                { (tri< q<q' q≢q' q≯q') → ⊥-elim (n≮n n (<-trans (proj₂ <-resp₂-≡ (sym eq) ( <-trans ((+-monoˡ-< (q * suc m) r<sm)) {!!})) ({!!})))
                ; (tri≈ q≮q' q≡q' q≯q') → q≡q'
                ; (tri> q≮q' q≢q' q>q') → ⊥-elim (n≮n n {!!})})))

divRemUniqueR : (m n : ℕ) → m ≡ 0 ⊎ ∃[ q ] ∃! _≡_ λ r → ( r < m × n ≡ r + q * m )
divRemUniqueR zero n = inj₁ refl
divRemUniqueR (suc m) n with divRem (suc m) n
... | inj₂ (q , r , r<sm , eq) = inj₂ (q , (r , ((r<sm , eq) ,
  λ {y} (y<sm , eq_y) → +-cancelʳ-≡ {(q * suc m)} r y (trans (sym eq) eq_y))))

divRemUnique : (m n : ℕ) → m ≡ 0 ⊎ ∃! _≡_ λ q → ( ∃! _≡_ λ r → ( r < m × n ≡ r + q * m ) )
divRemUnique zero n = inj₁ refl
divRemUnique (suc m) n with divRemUniqueQ (suc m) n
... | inj₂ (q , (r , r<sm , eq) , uniqueq) = inj₂ (q , ((r , ((r<sm , eq) , {!!})) ,  {!!}))
--... | inj₂ (q , r , r<sm , eq) = inj₂ (q , (r , ((r<sm , eq) ,
--   λ {y} (y<sm , eq_y) → +-cancelʳ-≡ {(q * suc m)} r y (trans (sym eq) eq_y))))


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

-- ∣*→r≡0 : (e : m ≢ 0) → m ∣* n → proj₁ (proj₂ (divRemUniqueR' m n e)) ≡ 0
-- ∣*→r≡0 {m} {n} m≢0 m∣*n with divRemUnique' m n m≢0
-- ∣*→r≡0 {m} {.(k * m)} m≢0 (m∣k*m k) | q , r , (r<m , eq) , u = {!!}

r≡0→∣* : (e : m ≢ 0) → proj₁ (proj₂ (divRem' m n e)) ≡ 0 → m ∣* n
r≡0→∣* {m} {n}  m≢0 r≡0 with (divRem' m n m≢0)
... | q , r , r<m , eq = subst (m ∣*_) (sym(trans eq (cong (_+ q * m) r≡0))) (m∣k*m q)



_∣*?_ : (m n : ℕ) → Dec(m ∣* n)
zero ∣*? zero = yes (m∣k*m 0)
zero ∣*? suc n = no z∤*s
m@(suc m₁) ∣*? n with divRem' m n (1+n≢0 {m₁})
... | q , zero , z<m , eq = yes (subst (m ∣*_) (sym eq) (m∣k*m q))
... | q , suc r , r<m , eq = no λ m∣n → {!!}


-----prime numbers

prime : ℕ → Set
prime n = ∀ {m : ℕ} → n ≢ 1 → m ∣* n → m ≡ 1 ⊎ m ≡ n

prime_or_one : ℕ → Set
prime_or_one n = ∀ {m : ℕ} → m ∣* n → m ≡ 1 ⊎ m ≡ n

prime' : ℕ → Set
prime' n = ( n ≢ 1 ) × ( prime_or_one n )

-----idea : list_of_divisors
----- p prime iff lod has 2 elements
----- if d | n, then l(d) subset of l(n)
----- => min l(n)-{1} is prime-divisor of n

record list_of_divisors (n : ℕ) : Set where
  field list     : List ( Σ ℕ ( _∣* n) )
        complete : ∀ k → k ∣* n → k ∈ Data.List.map proj₁ list
open list_of_divisors

module _ {A : Set} {P : A → Set} (P? : Decidable P) where

  filterWithProof : List A → List (Σ A P)
  filterWithProof [] = []
  filterWithProof (x ∷ xs) = case P? x of λ
    { (no ¬p) → filterWithProof xs ;
      (yes p) → (x , p) ∷ filterWithProof xs }

  filterWithProof→filter : (xs : List A)
    → Data.List.map proj₁ (filterWithProof xs) ≡ (filter P? xs)
  filterWithProof→filter [] = refl
  filterWithProof→filter (x ∷ xs) with P? x
  ... | no ¬p = filterWithProof→filter xs
  ... | yes p = cong (x ∷_) (filterWithProof→filter xs)

construct_list_of_divisors : (n : ℕ) → n ≢ 0 → list_of_divisors n
construct_list_of_divisors 0 n≢0 = ⊥-elim (n≢0 refl)
construct_list_of_divisors n@(suc n₁) n≢0 = record {
  list = filterWithProof (_∣*? n) (upTo (suc n)) ;
  complete = λ k k∣*n → subst (k ∈_) (sym (filterWithProof→filter (_∣*? n) (upTo (suc n))))
           (∈-filter⁺ (_∣*? n) (∈-upTo⁺ (s≤s (∣*→≤' refl k∣*n))) k∣*n) }

just_divisors : (n : ℕ) → n ≢ 0 → List ℕ
just_divisors n n≢0 = Data.List.map proj₁ (list (construct_list_of_divisors n n≢0))

----p is prime iff lod = [1,p]

prime→twoDivisors : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → prime' p → just_divisors p p≢0 ≡ 1 ∷ p ∷ []
prime→twoDivisors zero p≢0 (p≢1 , primep) = ⊥-elim (p≢0 refl)
prime→twoDivisors p@(suc _) p≢0 (p≢1 , primep) with construct_list_of_divisors p p≢0
... | record { list = list ; complete = complete } = {!!}

twoDivisors→prime : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → (just_divisors p p≢0 ≡ 1 ∷ p ∷ []) → prime' p
twoDivisors→prime 0 p≢0 e = ⊥-elim (p≢0 refl)
twoDivisors→prime 1 p≢0 ()
twoDivisors→prime p@(suc (suc _)) p≢0 e with construct_list_of_divisors p p≢0 in eq
... | record { list = list ; complete = complete } = (λ p≡1 → 1+n≢0  (suc-injective p≡1)) ,
  λ {m} m∣*p → {!complete m m∣*p!}

--divisor→sublist : (n≢0 : n ≢ 0) → (d≢0 : d ≢ 0) → d ∣* n → k ∈ just_divisors d

one_smallest_divisor : ∀ (n : ℕ) → ∃[ d ] d ∣* n × (∀ (e : ℕ) → (e ∣* n) → d ≤ e )
one_smallest_divisor n = {!!} , ({!!} , {!!})

smallest_divisor_is_prime : ∀ (n : ℕ) → ∀ (d : ℕ) → d ∣* n × (∀ (e : ℕ) → (e ∣* n) → d ≤ e ) → prime d
smallest_divisor_is_prime n d p = {!!}


-- at_least_one_divisor : ∀ (n : ℕ) → n ≥ 2 → ∃[ p ] p ∣* n × prime p
-- at_least_one_divisor n@(suc (suc k)) (s≤s (s≤s z≤n)) = (foldl helper {!!} (downFrom n) , ({!!} , {!!})
--   where helper : ℕ → ℕ → ℕ
--         helper a b with b ∣*? n
--         ... | no ¬p = {!!}
--         ... | yes p = {!!}

-- teilerliste : ∀ (n : ℕ) → List ℕ
-- teilerliste n = filter (_∣*? n) (filter (2 ≤?_) (upTo n))

-- min1Teiler : ∀ (n : ℕ) → n ≥ 2 → ¬( teilerliste n ≡ [])
-- min1Teiler .(suc (suc _)) (s≤s (s≤s z≤n)) = {!!}

-- minList : List ℕ → ℕ
-- minList [] = 0
-- minList (x ∷ []) = x
-- minList (x ∷ x₁ ∷ l) = x ⊓ minList (x₁ ∷ l)

-- {-# TERMINATING #-}
-- mininList' : ∀ (l : List ℕ) → l ≡ [] ⊎ minList l ∈ l
-- mininList' [] = inj₁ refl
-- mininList' (x ∷ []) = inj₂ (here refl)
-- mininList' (x ∷ x₁ ∷ l) = case x ≤? minList (x₁ ∷ l) of λ { (no ¬p) → inj₂ (case mininList' (x₁ ∷ l) of λ { (inj₂ y) → there (subst (_∈ (x₁ ∷ l)) (sym(m≥n⇒m⊓n≡n(≰⇒≥ ¬p))) y) }) ; (yes p) → inj₂ (here (m≤n⇒m⊓n≡m p)) }
-- --mininList' (zero ∷ l) = inj₂ (here refl)
-- --mininList' (suc x ∷ l) = inj₂ {!!}

-- mininList : ∀ (l : List ℕ) → ¬ l ≡ [] → minList l ∈ l
-- mininList [] e = ⊥-elim (e refl)
-- mininList (x ∷ l) e with mininList l
-- ... | e' = {!!}

-- --min2teiler : ∀ (n : ℕ) → 

-- primteiler : ∀ (n : ℕ) → n ≥ 2 → ∃[ p ] p ∣* n × prime p
-- primteiler n e = foldl _⊓_ n (teilerliste n) , {!!} , {!!}

-- --lemma : ∀ (m n k p : ℕ) → k ≤ n → ¬ k ∣ m → p ∣ m → prim p → n < p


-- infprim : ∀ (n : ℕ) → ∃[ p ] n ≤ p × prime p
-- infprim n = {!!}
