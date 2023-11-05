module prim where

--open import Relation.Binary.Reasoning.StrictPartialOrder
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬ ; All¬⇒¬Any)
import Data.List.Relation.Unary.AllPairs as AllPairs 
import Relation.Nullary.Decidable as Dec
open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.AllPairs.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Binary.Definitions hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary using (Decidable)

open import divisible
open import divRem


variable
  d k l m n o p : ℕ


-----prime numbers

irreducible : ℕ → Set
irreducible n = ∀ {m : ℕ} → m ∣ n → m ≡ 1 ⊎ m ≡ n

prime : ℕ → Set
prime n = (n ≢ 0) × ( n ≢ 1 ) × ( irreducible n )

----some properties

p>1 : prime p → p > 1
p>1 {zero}    (p≢0 , p≢1 , irred) = ⊥-elim (p≢0 refl)
p>1 {(suc 0)} (p≢0 , p≢1 , irred) = ⊥-elim (p≢1 refl)
p>1 {p@(suc (suc _))} prime       = s≤s (s≤s z≤n)

------list of divisors

sorted? : List ℕ → Set
sorted? = AllPairs.AllPairs _<_

record divList (n : ℕ) : Set where
  field list      : List ℕ
        complete₁ : k ∈ list → k ∣ n
        complete₂ : k ∣ n → k ∈ list
        sorted    : sorted? list
open divList

upTo-sorted : ∀ n → sorted? (upTo n)
upTo-sorted n = applyUpTo⁺₁ id n λ i<j j<n → i<j

mk-divList : ∀ n → n ≢ 0 → divList n
mk-divList zero n≢0 = ⊥-elim (n≢0 refl)
mk-divList n@(suc _) n≢0 = record { list =  filter (_∣? n) (upTo (suc n))
                                  ; complete₁ = λ k∈list → proj₂ (∈-filter⁻ (_∣? n) {xs = upTo(suc n)} k∈list)
                                  ; complete₂ = λ k∣n → ∈-filter⁺ (_∣? n) {xs = upTo (suc n)} (∈-upTo⁺ (s≤s (A⊎B⇒¬A⇒B (∣⇒≤ k∣n) 1+n≢0))) k∣n
                                  ; sorted = filter⁺ (_∣? n) (upTo-sorted (suc n))}


x∉[] : {A : Set} → {x : A} → x ∉ []
x∉[] = λ ()

sorted⇒samelist : ∀ (a b : List ℕ) → All.All (_∈ b) a × All.All (_∈ a) b → (sorted? a × sorted? b) → a ≡ b 
sorted⇒samelist [] [] (a⊂b , b⊂a) (sa , sb) = refl
sorted⇒samelist [] (x ∷ b) (a⊂b , b⊂a) (sa , sb) = ⊥-elim (x∉[] (All.head b⊂a))
sorted⇒samelist (x ∷ a) [] (a⊂b , b⊂a) (sa , sb) = ⊥-elim (x∉[] (All.head a⊂b))
sorted⇒samelist (x ∷ a) (y ∷ b) (xa⊂yb , yb⊂xa) (sxa , syb)
  = let x≡y = case (All.head xa⊂yb , All.head yb⊂xa) of λ { (here x≡y , snd) → x≡y
                                                        ; (there x∈b , here y≡x) → sym y≡x
                                                        ; (there x∈b , there y∈a) → ⊥-elim (<-asym (All.lookup (AllPairs.head sxa) y∈a) (All.lookup (AllPairs.head syb) x∈b)) }
        ∈yb∧>y⇒∈b = All.zipWith {P = _∈ y ∷ b} {Q = _> y} {R = _∈ b} λ { (∈yb , >y) → case ∈yb of λ { (here ≡y) → ⊥-elim (<⇒≢ >y (sym ≡y)) ; (there ∈b) → ∈b } }
        a⊂b = ∈yb∧>y⇒∈b ((All.tail xa⊂yb) , subst (λ z → All.All (z <_) a) x≡y (AllPairs.head sxa))
        ∈xa∧>x⇒∈a = All.zipWith {P = _∈ x ∷ a} {Q = _> x} {R = _∈ a} λ { (∈xa , >x) → case ∈xa of λ { (here ≡x) → ⊥-elim (<⇒≢ >x (sym ≡x)) ; (there ∈a) → ∈a } }
        b⊂a = ∈xa∧>x⇒∈a ((All.tail yb⊂xa) , subst (λ z → All.All (z <_) b) (sym x≡y) (AllPairs.head syb))
    in cong₂ _∷_ x≡y (sorted⇒samelist a b ( a⊂b  , b⊂a) ((AllPairs.tail sxa) , (AllPairs.tail syb)))

unique-divList : ∀ n → (a b : divList n) → list a ≡ list b
unique-divList n record { list = list-a ; complete₁ = complete₁-a ; complete₂ = complete₂-a ; sorted = sorted-a }
                 record { list = list-b ; complete₁ = complete₁-b ; complete₂ = complete₂-b ; sorted = sorted-b }
  = sorted⇒samelist list-a list-b ( All.tabulate (λ k∈l-a → complete₂-b (complete₁-a k∈l-a) )
                                  , All.tabulate (λ k∈l-b → complete₂-a (complete₁-b k∈l-b))) (sorted-a , sorted-b)


2divs→prime : ∀ (p : ℕ) → (p≢0 : p ≢ 0) → (ds : divList p) → list ds ≡ 1 ∷ p ∷ [] → prime p
2divs→prime zero p≢0 ds e             = ⊥-elim (p≢0 refl)
2divs→prime (suc zero) p≢0 record { list = .(1 ∷ 1 ∷ []) ; sorted = sorted } refl = ⊥-elim (n≮n 1 $ All.head $ AllPairs.head sorted)
2divs→prime p@(suc (suc _)) p≢0 record { list = .(1 ∷ p ∷ []) ; complete₂ = complete₂ } refl
  = p≢0 , 1+n≢0 ∘ suc-injective
        , λ {k} k∣p → case complete₂ k∣p of λ { (here k≡1) → inj₁ k≡1 ; (there (here k≡p)) → inj₂ k≡p}

2-prime : prime 2
2-prime = 2divs→prime 2 (λ ()) (mk-divList 2 λ ()) refl

head≡1 : ∀ n → n ≢ 0 → n ≢ 1 → (ds : divList n) → ∃[ l ] list ds ≡ 1 ∷ l × l ≢ [] 
head≡1 zero n≢0 n≢1 ds = ⊥-elim (n≢0 refl)
head≡1 (suc zero) n≢0 n≢1 ds = ⊥-elim (n≢1 refl)
head≡1 n@(suc (suc _)) n≢0 n≢1 record { list = [] ; complete₂ = complete₂ }
  = ⊥-elim (x∉[] (complete₂ o∣m))
head≡1 n@(suc (suc _)) n≢0 n≢1 record { list = (zero ∷ list₁) ; complete₁ = complete₁ }
  = ⊥-elim (z∤s (complete₁ (here refl)))
head≡1 n@(suc (suc _)) n≢0 n≢1 record { list = (suc zero ∷ []) ; complete₂ = complete₂ }
  = ⊥-elim (case complete₂ m∣m of λ { (here px) → n≢1 px ; (there x) → x∉[] x})
head≡1 n@(suc (suc _)) n≢0 n≢1 record { list = (suc zero ∷ x ∷ list₁) ; complete₂ = complete₂ }
  = x ∷ list₁ , refl , λ ()
head≡1 n@(suc (suc _)) n≢0 n≢1 record { list = (suc (suc x) ∷ list₁) ; complete₂ = complete₂ ; sorted = sorted }
  = let 1∈list = complete₂ o∣m
        1∈rest = case 1∈list of λ { (there 1∈r) → 1∈r }
    in case All.lookup (AllPairs.head sorted) 1∈rest of λ { (s≤s ())}


∃-prime-divisor : ∀ (n : ℕ) → n ≢ 1 → ∃[ p ] p ∣ n × prime p
∃-prime-divisor zero n≢1 = 2 , ((m∣k*m zero) , 2-prime)
∃-prime-divisor (suc zero) n≢1 = ⊥-elim (n≢1 refl)
∃-prime-divisor n@(suc (suc _)) n≢1 with ds ← mk-divList n 1+n≢0 | head≡1 n 1+n≢0 n≢1 ds
... | l , list≡1∷l  , l≢0 with ds
... | record { list = suc zero ∷ [] ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted } = ⊥-elim (case list≡1∷l of λ { refl → l≢0 refl})
... | record { list = suc zero ∷ p ∷ list₁ ; complete₁ = complete₁ ; complete₂ = complete₂ ; sorted = sorted }
 = let p∣n = complete₁ (there (here refl))
       p>1 = All.head (AllPairs.head sorted)
       p≢0 = >⇒≢ (<-trans (s≤s z≤n) p>1)
       p≢1 = >⇒≢ p>1
       p<rest = AllPairs.head (AllPairs.tail sorted)
       m≤p = λ {m} (m∣p : m ∣ p) → A⊎B⇒¬A⇒B (∣⇒≤ m∣p) p≢0
       m∈list = λ {m} (m∣p : m ∣ p) → complete₂ (∣-trans m∣p p∣n)
   in p , (p∣n , ( p≢0 , p≢1
  , λ {m} m∣p → case m∈list m∣p of λ { (here m≡1) → inj₁ m≡1
                                     ; (there (here m≡p)) → inj₂ m≡p
                                     ; (there (there m∈rest)) → ⊥-elim (All¬⇒¬Any (All.map (λ p< → <⇒≢ (≤-trans (s≤s (m≤p m∣p)) p<)) p<rest) m∈rest)}))


fac : ℕ → ℕ
fac 0 = 1
fac (suc n) = (suc n) * fac n

fac≢0 : ∀ n → fac n ≢ 0
fac≢0 zero = λ ()
fac≢0 (suc n) = λ eq → fac≢0 n (m+n≡0⇒m≡0 (fac n) eq)

k∣facn : ∀ k → k ≢ 0 → ∀ n → k ≤ n → k ∣ fac n
k∣facn zero k≢0 n k≤n = ⊥-elim (k≢0 refl)
k∣facn  k@(suc _) k≢0 n k≤n = helper n (≤⇒≤′ k≤n)
  where helper : ∀ n → k ≤′ n → k ∣ fac n
        helper n ≤′-refl = m∣m*k _
        helper n@(suc n₁) (≤′-step e) = ∣-trans (helper n₁ e) (m∣k*m (suc n₁))


infprim : ∀ (n : ℕ) → ∃[ p ] n ≤ p × prime p
infprim n = let N = suc (fac n)
                N≢1 = λ N≡1 → fac≢0 n (suc-injective N≡1)
                p , (p∣N , primep) = ∃-prime-divisor N N≢1
                p≢0 = proj₁ primep
  in case p <? n of λ
  { (no p≮n)  → p , ((≮⇒≥ p≮n) , primep)
  ; (yes p<n) → ⊥-elim (m∣n⇒m∤1+n (p>1 primep) (k∣facn p p≢0 n (<⇒≤ p<n)) p∣N) }
