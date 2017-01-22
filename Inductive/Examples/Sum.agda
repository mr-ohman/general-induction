module Inductive.Examples.Sum where

open import Inductive
open import Tuple

open import Data.Fin
open import Data.Product
open import Data.List
open import Data.Vec

_⊎_ : Set → Set → Set
A ⊎ B = Inductive (((A ∷ []) , []) ∷ (((B ∷ []) , []) ∷ []))

inl : {A B : Set} → A → A ⊎ B
inl a = construct zero (a ∷ []) []

inr : {A B : Set} → B → A ⊎ B
inr b = construct (suc zero) (b ∷ []) []

case : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
case x f g = rec (f ∷ (g ∷ [])) x
