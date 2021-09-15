open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.String

module Live where
{-
  data Tag: Type where
    `unit    : Tag
    `nat     : Tag
    `string  : Tag
    `list    : Tag → Tag
    _`x_     : Tag → Tag → Tag

  exampletag : Tag
  exampletag = `nat `x (`list `string)

  Data : Tag → Type
  Data t = ?



-}
  data Tag : Set where
    `nat     : Tag
    `string  : Tag
    _`x_     : Tag → Tag → Tag

  exampletag : Tag
  exampletag = `nat `x (`list `string)

  Data : Tag → Set
  Data `nat = Nat
  Data `string = String
  Data (t `x t₁) = Data t `x Data t₁
