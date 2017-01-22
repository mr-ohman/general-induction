module Inductive.Examples.BinTree where

open import Inductive
open import Tuple

open import Data.Fin
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Data.Vec hiding (map)

BinTree : Set → Set
BinTree A = Inductive (([] , []) ∷ (((A ∷ []) , ([] ∷ ([] ∷ []))) ∷ []))

leaf : {A : Set} → BinTree A
leaf = construct zero [] []

node : {A : Set} → A → BinTree A → BinTree A → BinTree A
node a lt rt = construct (suc zero) (a ∷ []) ((λ _ → lt) ∷ ((λ _ → rt) ∷ []))

map : {A B : Set} → (A → B) → BinTree A → BinTree B
map f = rec (leaf ∷ ((λ a lt rlt rt rrt → node (f a) rlt rrt) ∷ []))

import Inductive.Examples.List as List

dfs : {A : Set} → BinTree A → List.List A
dfs = rec ( List.nil
          ∷ (λ a lt rlt rt rrt → List.cons a (rlt List.++ rrt))
          ∷ [])
