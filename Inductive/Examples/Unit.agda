module Inductive.Examples.Unit where

open import Inductive
open import Tuple

open import Data.Fin
open import Data.Product
open import Data.List
open import Data.Vec

⊤ : Set
⊤ = Inductive (([] , []) ∷ [])

unit : ⊤
unit = construct zero [] []
