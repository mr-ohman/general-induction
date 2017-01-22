module Inductive where

open import Level using (_⊔_)
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.List hiding (map)
import Data.List as List
open import Data.Vec hiding (_++_)
open import Data.Product hiding (map)
open import Tuple using (Tuple; []; _∷_; unfoldToFunc; apply; proof₁; proof₂)

Const : Set₁
Const = List Set × List (List Set)

data TupleRec (A : Set) : List (List Set) → Set where
  [] : TupleRec A []
  _∷_ : ∀ {x xs} → ((Tuple x) → A) → TupleRec A xs → TupleRec A (x ∷ xs)

data Inductive {n} (A : Vec Const n) : Set where
  construct : (m : Fin n)
              (x : Tuple (proj₁ (lookup m A)))
              (r : TupleRec (Inductive A) (proj₂ (lookup m A)))
            → Inductive A

unfoldToConFunc : List (List Set) → Set → Set
unfoldToConFunc [] B = B
unfoldToConFunc (As ∷ As₁) B = (unfoldToFunc As B) → unfoldToConFunc As₁ B

unfoldToRecFunc : List (List Set) → Set → Set → Set
unfoldToRecFunc [] B C = C
unfoldToRecFunc (As ∷ As₁) B C = (unfoldToFunc As B) → (unfoldToFunc As C) →
                                 unfoldToRecFunc As₁ B C

proofCon : (As : List (List Set)) {B : Set}
         → (TupleRec B As → B) → unfoldToConFunc As B
proofCon [] B₁ = B₁ []
proofCon (As ∷ As₁) B₁ x = proofCon As₁ (λ x₁ → B₁ (proof₂ As x ∷ x₁))

-- The constrution function of an inductive instance
ConFunc : Set → Const → Set
ConFunc A (proj₁ , proj₂) = unfoldToFunc proj₁ (unfoldToConFunc proj₂ A)

-- The recursion function of an inductive instance
RecFunc : Set → Set → Const → Set
RecFunc A B (proj₁ , proj₂) = unfoldToFunc proj₁ (unfoldToRecFunc proj₂ A B)

recapply : ∀ {n} {A : Vec Const n} {B : Set}
        {L : List Set} {R : List (List Set)}
      → RecFunc (Inductive A) B (L , R)
      → Tuple L → TupleRec (Inductive A) R → TupleRec B R → B
recapply {L = []} {[]} f [] [] [] = f
recapply {L = []} {R ∷ Rs} f [] (x ∷ x₁) (x₂ ∷ x₃) =
  recapply {L = []} {R = Rs} (f (proof₁ R x) (proof₁ R x₂)) [] x₁ x₃
recapply {L = _ ∷ _} f (x₁ ∷ x₂) r c = recapply (f x₁) x₂ r c

rec : ∀ {n} {A : Vec Const n} {B : Set}
    → Tuple (toList (map (RecFunc (Inductive A) B) A))
    → Inductive A → B
rec {n} {A} {B} fs (construct m x r) = rec' A fs m x r
  where mapRec : ∀ {m} → TupleRec (Inductive A) m → TupleRec B m
        mapRec {m = []} [] = []
        mapRec {m = _ ∷ _} (x₁ ∷ r₁) = (λ x₂ → rec fs (x₁ x₂)) ∷ mapRec r₁
        rec' : ∀ {m}
             → (A' : Vec Const m)
             → Tuple (toList (map (RecFunc (Inductive A) B) A'))
             → (m' : Fin m)
             → Tuple (proj₁ (lookup m' A'))
             → TupleRec (Inductive A) (proj₂ (lookup m' A'))
             → B
        rec' [] fs () x r
        rec' (_ ∷ A') (f ∷ fs) zero x r = recapply f x r (mapRec r)
        rec' (_ ∷ A') (f ∷ fs) (suc m) x r = rec' A' fs m x r
