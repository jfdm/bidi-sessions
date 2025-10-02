module Extra

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem


noHR : (the (Elem x (xs :< x)) Here) = the (Elem y (ys :< y')) (There z) -> Void
noHR Refl impossible

noRH : the (Elem y (ys :< y')) (There z) = (the (Elem x (xs :< x)) Here) -> Void
noRH Refl impossible

public export
decEq : {0 xs : SnocList a}
     -> (ix : Elem x xs)
     -> (yx : Elem y xs)
     -> Dec (ix = yx)
decEq Here Here
  = Yes Refl
decEq Here (There z)
  = No noHR
decEq (There z) Here
  = No noRH
decEq (There z) (There y) with (decEq z y)
  decEq (There z) (There z) | (Yes Refl) = Yes Refl
  decEq (There z) (There y) | (No contra)
    = No (\case Refl => contra Refl)


namespace List

  public export
  data Shape : (xs,ys : List a) -> Type
    where
      End : Shape [] []
      LH : Shape (x::xs) Nil
      RH : Shape Nil (y::ys)
      B : Shape (x::xs) (y::ys)

  export
  shape : (xs, ys : List a ) -> Shape xs ys
  shape [] [] = End
  shape [] (x :: xs) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = B


-- [ EOF ]
