module Inductive.Examples.List where

open import Inductive
open import Tuple hiding (_++_)

open import Data.Fin
open import Data.Product hiding (map)
open import Data.List hiding (List; map; foldr; _++_)
open import Data.Vec hiding (map; foldr; _++_)

List : Set → Set
List A = Inductive (([] , []) ∷ (((A ∷ []) , ([] ∷ [])) ∷ []))

nil : {A : Set} → List A
nil = construct zero [] []

cons : {A : Set} → A → List A → List A
cons x xs = construct (suc zero) (x ∷ []) ((λ _ → xs) ∷ [])

map : {A B : Set} → (A → B) → List A → List B
map f = rec (nil ∷ ((λ a as ras → cons (f a) ras) ∷ []))

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f b = rec (b ∷ (λ a as ras → f a ras) ∷ [])

_++_ : {A : Set} → List A → List A → List A
xs ++ ys = rec (ys ∷ (λ a as ras → cons a ras) ∷ []) xs
