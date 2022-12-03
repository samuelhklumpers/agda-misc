{-# OPTIONS --no-termination-check #-}

module Pairing where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Empty

private variable
  a b c : Level
  A B C : Set a

π' : ℕ → ℕ → ℕ
π' n       (suc m) = suc (π' (suc n) m)
π' 0       0       = 0
π' (suc n) 0       = suc (π' 0 n)

π : ℕ × ℕ → ℕ
π (n , m) = π' n m

unπ' : ℕ → ℕ × ℕ → ℕ × ℕ
unπ' 0       (n     , m) = n , m
unπ' (suc i) (0     , n) = unπ' i (suc n , 0)
unπ' (suc i) (suc n , m) = unπ' i (n , suc m)

unπ : ℕ → ℕ × ℕ
unπ i = unπ' i (0 , 0)

ret' : ∀ i n m → π (unπ' i (n , m)) ≡ i + π (n , m)
ret' 0       n       m = refl
ret' (suc i) 0       m = trans (ret' i (suc m) 0) (+-suc i (π' zero m))
ret' (suc i) (suc n) m = trans (ret' i n (suc m)) (+-suc i (π' (suc n) m))

inj-l : ∀ n k m l → π' n k ≡ π' m l → n ≡ m
inj-r : ∀ n k m l → π' n k ≡ π' m l → k ≡ l

inj-l n     (suc k) m     (suc l) e = suc-injective (inj-l _ _ _ _ (suc-injective e))
inj-l n     (suc k) (suc m) 0     e = ⊥-elim (0≢1+n (sym (inj-l _ _ _ _ (suc-injective e))))
inj-l 0     0     0     0     e = refl
inj-l (suc n) 0     m     (suc l) e = ⊥-elim (0≢1+n (inj-l _ _ _ _ (suc-injective e)))
inj-l (suc n) 0     (suc m) 0     e = cong suc (inj-r _ _ _ _ (suc-injective e))

inj-r n     (suc k) m     (suc l) e = cong suc (inj-r _ _ _ _ (suc-injective e))
inj-r n     (suc k) (suc m) 0     e = ⊥-elim (0≢1+n (sym (inj-l _ _ _ _ (suc-injective e))))
inj-r 0     0     0     0     e = refl
inj-r (suc n) 0     m     (suc l) e = ⊥-elim (0≢1+n (inj-l _ _ _ _ (suc-injective e)))
inj-r (suc n) 0     (suc m) 0     e = refl

inj : ∀ p q → π p ≡ π q → p ≡ q
inj (_ , _) (_ , _) e = cong₂ _,_ (inj-l _ _ _ _ e) (inj-r _ _ _ _ e)

-- π is a bijection :)
ret : ∀ i → π (unπ i) ≡ i
ret i = trans (ret' i 0 0) (+-identityʳ _)

sec : ∀ p → unπ (π p) ≡ p
sec p = inj (unπ (π p)) p (ret (π p))
