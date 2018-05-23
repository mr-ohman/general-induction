module Tuple where

import Level
import Data.List as List
open import Data.List hiding (_++_; [_]; _∷ʳ_)
open import Data.Fin

open import Relation.Binary.PropositionalEquality hiding ([_])

infixr 5 _∷_

data Tuple {a} : List (Set a) → Set a where
  [] : Tuple []
  _∷_ : ∀ {A As} → A → Tuple As → Tuple (A ∷ As)

[_] : ∀ {a} {A : Set a} → A → Tuple (A ∷ [])
[ x ] = x ∷ []

_++_ : ∀ {a} {xs ys : List (Set a)}
     → Tuple xs → Tuple ys → Tuple (xs List.++ ys)
_++_ {xs = []} [] ys = ys
_++_ {xs = _ ∷ _} (x ∷ xs) ys = x ∷ (xs ++ ys)

_∷ʳ_ : ∀ {a} {x : Set a} {xs : List (Set a)}
     → Tuple xs → x → Tuple (xs List.∷ʳ x)
_∷ʳ_ xs x = xs ++ [ x ]

private
  listLookup : ∀ {a} {A : Set a} (xs : List A) → (n : Fin (length xs)) → A
  listLookup [] ()
  listLookup (x ∷ xs) zero = x
  listLookup (x ∷ xs) (suc n) = listLookup xs n

lookup : ∀ {a} {xs : List (Set a)}
       → (n : Fin (length xs)) → Tuple xs → listLookup xs n
lookup {xs = []} () []
lookup {xs = _ ∷ _} zero (x ∷ xs) = x
lookup {xs = _ ∷ _} (suc n) (x ∷ xs) = lookup n xs

unfoldToFunc : ∀ {a} → List (Set a) → Set a → Set a
unfoldToFunc [] B = B
unfoldToFunc (A ∷ As) B = A → unfoldToFunc As B

apply : {Xs : List Set} {A : Set} → unfoldToFunc Xs A → Tuple Xs → A
apply {[]} f [] = f
apply {_ ∷ _} f (x ∷ xs) = apply (f x) xs

list-proof : ∀ {a} {A : Set a} (xs : List A) → xs ≡ (xs List.++ [])
list-proof [] = refl
list-proof (x ∷ xs) = cong (_∷_ x) (list-proof xs)

list-proof₁ : ∀ {a} {A : Set a} (xs ys zs : List A)
            → (xs List.++ ys) List.++ zs ≡ xs List.++ (ys List.++ zs)
list-proof₁ [] ys zs = refl
list-proof₁ (x ∷ xs) ys zs = cong (_∷_ x) (list-proof₁ xs ys zs)

curry : ∀ {a} (xs : List (Set a)) → unfoldToFunc xs (Tuple xs)
curry xs = curry' [] xs []
  where curry' : ∀ {a} (xs ys : List (Set a)) → Tuple xs
               → unfoldToFunc ys (Tuple (xs List.++ ys))
        curry' xs [] tpl = subst Tuple (list-proof xs) tpl
        curry' xs (y ∷ ys) tpl x₁ =
          subst (λ x → unfoldToFunc ys (Tuple x))
                (list-proof₁ xs List.[ y ] ys)
                (curry' (xs List.∷ʳ y) ys (tpl ∷ʳ x₁))

proof₁ : ∀ {a} (As : List (Set a)) {B : Set a}
       → (Tuple As → B) → unfoldToFunc As B
proof₁ [] f = f []
proof₁ (A ∷ As) f x = proof₁ As (λ xs → f (x ∷ xs))

proof₂ : ∀ {a} (As : List (Set a)) {B : Set a}
       → unfoldToFunc As B → Tuple As → B
proof₂ [] f [] = f
proof₂ (A ∷ As) f (x ∷ xs) = proof₂ As (f x) xs
