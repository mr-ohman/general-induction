module Inductive.Examples.Ord where

open import Inductive
open import Tuple

open import Data.Fin
open import Data.Product
open import Data.List
open import Data.Vec hiding (lookup)

open import Inductive.Examples.Nat

Ord : Set
Ord = Inductive (([] , []) ∷ (([] , ((Nat ∷ []) ∷ [])) ∷ []))

zeroₒ : Ord
zeroₒ = construct Fin.zero [] []

supₒ : (Nat → Ord) → Ord
supₒ f = construct (Fin.suc Fin.zero) [] ((λ x → f (lookup Fin.zero x)) ∷ [])
