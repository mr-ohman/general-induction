module Inductive.Examples.Nat where

open import Inductive
open import Tuple

import Data.Fin as Fin
open import Data.Product
open import Data.List
open import Data.Vec hiding (lookup)

Nat : Set
Nat = Inductive ( ([] , []) ∷ (([] , ([] ∷ [])) ∷ []))

zero : Nat
zero = construct Fin.zero [] []

suc : Nat → Nat
suc n = construct (Fin.suc Fin.zero) [] ((λ _ → n) ∷ [])

_+_ : Nat → Nat → Nat
n + m = rec (m ∷ ((λ x x₁ → suc x₁) ∷ [])) n
