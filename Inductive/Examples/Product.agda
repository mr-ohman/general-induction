module Inductive.Examples.Product where

open import Inductive
open import Tuple

open import Data.Fin
open import Data.Product hiding (_×_; <_,_>)
open import Data.List
open import Data.Vec

_×_ : Set → Set → Set
A × B = Inductive (((A ∷ (B ∷ [])) , []) ∷ [])

<_,_> : {A B : Set} → A → B → A × B
< a , b > = construct zero (a ∷ (b ∷ [])) []

fst : {A B : Set} → A × B → A
fst = rec ((λ a b → a) ∷ [])

snd : {A B : Set} → A × B → B
snd = rec ((λ a b → b) ∷ [])
