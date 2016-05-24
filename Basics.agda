data day : Set where
  monday : day
  tuesday : day
  wednesday : day
  thursday : day
  friday : day
  saturday : day
  sunday : day

nextWeekday : day → day
nextWeekday monday = tuesday
nextWeekday tuesday = wednesday
nextWeekday wednesday = thursday
nextWeekday thursday = friday
nextWeekday friday = monday
nextWeekday saturday = monday
nextWeekday sunday = monday

record test1 : Set where
  open import Relation.Binary.PropositionalEquality

  testNextWeekday : nextWeekday (nextWeekday saturday) ≡ tuesday
  testNextWeekday = refl

data bool : Set where
  true : bool
  false : bool

infixr 20 ¬_
infixl 10 _∧_
infixl 9 _∨_

¬_ : bool → bool
¬ true = false
¬ false = true

_∧_ : bool → bool → bool
true ∧ b₂ = b₂
false ∧ _ = false

_∨_ : bool → bool → bool
true ∨ _ = true
false ∨ b₂ = b₂

record test2 : Set where
  open import Relation.Binary.PropositionalEquality

  testORb1 : true ∨ false ≡ true
  testORb1 = refl
  testORb2 : false ∨ false ≡ false
  testORb2 = refl
  testORb3 : false ∨ true ≡ true
  testORb3 = refl
  testORb4 : true ∨ true ≡ true
  testORb4 = refl

nandb : bool → bool → bool
nandb true true = false
nandb _ _ = true

record test3 : Set where
  open import Relation.Binary.PropositionalEquality

  testNANDb1 : nandb true false ≡ true
  testNANDb1 = refl
  testNANDb2 : nandb false false ≡ true
  testNANDb2 = refl
  testNANDb3 : nandb false true ≡ true
  testNANDb3 = refl
  testNANDb4 : nandb true true ≡ false
  testNANDb4 = refl

open import Relation.Binary.PropositionalEquality
open import Data.Product

Op₂ : Set → Set
Op₂ X = X → X → X
Assoc : {A : Set} → Op₂ A → Set
Assoc _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
Left-Identity : {A : Set} → Op₂ A → A → Set
Left-Identity _∙_ ε = ∀ x → ε ∙ x ≡ x
Right-Identity : {A : Set} → Op₂ A → A → Set
Right-Identity _∙_ ε = ∀ x → x ∙ ε ≡ x
Identity : {A : Set} → Op₂ A → A → Set
Identity _∙_ ε = Left-Identity _∙_ ε × Right-Identity _∙_ ε

record IsSemigroup (A : Set) (_∙_ : Op₂ A) : Set where
  field
    assoc : Assoc _∙_

∧-isSemigroup : IsSemigroup bool _∧_
∧-isSemigroup = record { assoc = associativity }
  where
    associativity : ∀ x y z → ((x ∧ y) ∧ z) ≡ (x ∧ (y ∧ z))
    associativity true y z = refl
    associativity false y z = refl

∨-isSemigroup : IsSemigroup bool _∨_
∨-isSemigroup = record { assoc = associativity }
  where
    associativity : ∀ x y z → ((x ∨ y) ∨ z) ≡ (x ∨ (y ∨ z))
    associativity true y z = refl
    associativity false y z = refl

record IsMonoid (A : Set) (_∙_ : Op₂ A) (ε : A) : Set where
  field
    isSemigroup : IsSemigroup A _∙_
    identity : Identity _∙_ ε

∧-true-isMonoid : IsMonoid bool _∧_ true
∧-true-isMonoid = record { isSemigroup = ∧-isSemigroup
                         ; identity = left-id , right-id
                         }
                where
                  left-id : ∀ x → x ≡ x
                  left-id x = refl
                  right-id : ∀ x → (x ∧ true) ≡ x
                  right-id true = refl
                  right-id false = refl
                  
∨-false-isMonoid : IsMonoid bool _∨_ false
∨-false-isMonoid = record { isSemigroup = ∨-isSemigroup
                          ; identity = left-id , right-id
                          }
                 where
                   left-id : ∀ x → x ≡ x
                   left-id x = refl
                   right-id : ∀ x → (x ∨ false) ≡ x
                   right-id true = refl
                   right-id false = refl

andb3 : bool → bool → bool → bool
andb3 x y z = x ∧ y ∧ z

record test4 : Set where
  open import Relation.Binary.PropositionalEquality

  testANDb31 : andb3 true true true ≡ true
  testANDb31 = refl
  testANDb32 : andb3 false true true ≡ false
  testANDb32 = refl
  testANDb33 : andb3 true false true ≡ false
  testANDb33 = refl
  testANDb34 : andb3 true true false ≡ false
  testANDb34 = refl
